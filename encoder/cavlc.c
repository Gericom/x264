/*****************************************************************************
 * cavlc.c: cavlc bitstream writing
 *****************************************************************************
 * Copyright (C) 2003-2017 x264 project
 *
 * Authors: Laurent Aimar <fenrir@via.ecp.fr>
 *          Loren Merritt <lorenm@u.washington.edu>
 *          Fiona Glaser <fiona@x264.com>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02111, USA.
 *
 * This program is also available under a commercial proprietary license.
 * For more information, contact us at licensing@x264.com.
 *****************************************************************************/

#include "common/common.h"
#include "macroblock.h"

#ifndef RDO_SKIP_BS
#define RDO_SKIP_BS 0
#endif

/* [400,420][inter,intra] */
static const uint8_t cbp_to_golomb[2][2][48] =
{
    {{ 0,  1,  2,  5,  3,  6, 14, 10,  4, 15,  7, 11,  8, 12, 13,  9 },
     { 1, 10, 11,  6, 12,  7, 14,  2, 13, 15,  8,  3,  9,  4,  5,  0 }},
    {{ 0,  2,  3,  7,  4,  8, 17, 13,  5, 18,  9, 14, 10, 15, 16, 11,
       1, 32, 33, 36, 34, 37, 44, 40, 35, 45, 38, 41, 39, 42, 43, 19,
       6, 24, 25, 20, 26, 21, 46, 28, 27, 47, 22, 29, 23, 30, 31, 12 },
     { 3, 29, 30, 17, 31, 18, 37,  8, 32, 38, 19,  9, 20, 10, 11,  2,
      16, 33, 34, 21, 35, 22, 39,  4, 36, 40, 23,  5, 24,  6,  7,  1,
      41, 42, 43, 25, 44, 26, 46, 12, 45, 47, 27, 13, 28, 14, 15,  0 }}
};

static const uint8_t mb_type_b_to_golomb[3][9]=
{
    { 4,  8, 12, 10,  6, 14, 16, 18, 20 }, /* D_16x8 */
    { 5,  9, 13, 11,  7, 15, 17, 19, 21 }, /* D_8x16 */
    { 1, -1, -1, -1,  2, -1, -1, -1,  3 }  /* D_16x16 */
};

static const uint8_t subpartition_p_to_golomb[4]=
{
    3, 1, 2, 0
};

static const uint8_t subpartition_b_to_golomb[13]=
{
    10,  4,  5,  1, 11,  6,  7,  2, 12,  8,  9,  3,  0
};

#define bs_write_vlc(s,v) bs_write( s, (v).i_size, (v).i_bits )

/****************************************************************************
 * x264_cavlc_block_residual:
 ****************************************************************************/
static inline int cavlc_block_residual_escape( x264_t *h, int i_suffix_length, int level )
{
    bs_t *s = &h->out.bs;
    static const uint16_t next_suffix[7] = { 0, 3, 6, 12, 24, 48, 0xffff };
    int i_level_prefix = 15;
    int mask = level >> 31;
    int abs_level = (level^mask)-mask;
    int i_level_code = abs_level*2-mask-2;
    if( ( i_level_code >> i_suffix_length ) < 15 )
    {
        bs_write( s, (i_level_code >> i_suffix_length) + 1 + i_suffix_length,
                 (1<<i_suffix_length) + (i_level_code & ((1<<i_suffix_length)-1)) );
    }
    else
    {
        i_level_code -= 15 << i_suffix_length;
        if( i_suffix_length == 0 )
            i_level_code -= 15;

        /* If the prefix size exceeds 15, High Profile is required. */
        if( i_level_code >= 1<<12 )
        {
            if( h->sps->i_profile_idc >= PROFILE_HIGH )
            {
                while( i_level_code > 1<<(i_level_prefix-3) )
                {
                    i_level_code -= 1<<(i_level_prefix-3);
                    i_level_prefix++;
                }
            }
            else
            {
#if RDO_SKIP_BS
                /* Weight highly against overflows. */
                s->i_bits_encoded += 2000;
#else
                /* We've had an overflow; note it down and re-encode the MB later. */
                h->mb.b_overflow = 1;
#endif
            }
        }
        bs_write( s, i_level_prefix + 1, 1 );
        bs_write( s, i_level_prefix - 3, i_level_code & ((1<<(i_level_prefix-3))-1) );
    }
    if( i_suffix_length == 0 )
        i_suffix_length++;
    if( abs_level > next_suffix[i_suffix_length] )
        i_suffix_length++;
    return i_suffix_length;
}

static int cavlc_block_residual_internal( x264_t *h, int ctx_block_cat, dctcoef *l, int nC )
{
    bs_t *s = &h->out.bs;
    static const uint8_t ctz_index[8] = {3,0,1,0,2,0,1,0};
    static const uint8_t count_cat[14] = {16, 15, 16, 0, 15, 64, 16, 15, 16, 64, 16, 15, 16, 64};
    x264_run_level_t runlevel;
    int i_total, i_trailing, i_total_zero, i_suffix_length;
    unsigned int i_sign;

    /* level and run and total */
    i_total = h->quantf.coeff_level_run[ctx_block_cat]( l, &runlevel );
    x264_prefetch( &x264_run_before[runlevel.mask] );
    i_total_zero = runlevel.last + 1 - i_total;

    /* branchless i_trailing calculation */
    runlevel.level[i_total+0] = 2;
    runlevel.level[i_total+1] = 2;
    i_trailing = ((((runlevel.level[0]+1) | (1-runlevel.level[0])) >> 31) & 1) // abs(runlevel.level[0])>1
               | ((((runlevel.level[1]+1) | (1-runlevel.level[1])) >> 31) & 2)
               | ((((runlevel.level[2]+1) | (1-runlevel.level[2])) >> 31) & 4);
    i_trailing = ctz_index[i_trailing];
    i_sign = ((runlevel.level[2] >> 31) & 1)
           | ((runlevel.level[1] >> 31) & 2)
           | ((runlevel.level[0] >> 31) & 4);
    i_sign >>= 3-i_trailing;

    /* total/trailing */
    bs_write_vlc( s, x264_coeff_token[nC][i_total-1][i_trailing] );

    i_suffix_length = i_total > 10 && i_trailing < 3;
    bs_write( s, i_trailing, i_sign );

    if( i_trailing < i_total )
    {
        int val = runlevel.level[i_trailing];
        int val_original = runlevel.level[i_trailing]+LEVEL_TABLE_SIZE/2;
        val -= ((val>>31)|1) & -(i_trailing < 3); /* as runlevel.level[i] can't be 1 for the first one if i_trailing < 3 */
        val += LEVEL_TABLE_SIZE/2;

        if( (unsigned)val_original < LEVEL_TABLE_SIZE )
        {
            bs_write_vlc( s, x264_level_token[i_suffix_length][val] );
            i_suffix_length = x264_level_token[i_suffix_length][val_original].i_next;
        }
        else
            i_suffix_length = cavlc_block_residual_escape( h, i_suffix_length, val-LEVEL_TABLE_SIZE/2 );
        for( int i = i_trailing+1; i < i_total; i++ )
        {
            val = runlevel.level[i] + LEVEL_TABLE_SIZE/2;
            if( (unsigned)val < LEVEL_TABLE_SIZE )
            {
                bs_write_vlc( s, x264_level_token[i_suffix_length][val] );
                i_suffix_length = x264_level_token[i_suffix_length][val].i_next;
            }
            else
                i_suffix_length = cavlc_block_residual_escape( h, i_suffix_length, val-LEVEL_TABLE_SIZE/2 );
        }
    }

    if( ctx_block_cat == DCT_CHROMA_DC )
    {
        if( i_total < 8>>CHROMA_V_SHIFT )
        {
            vlc_t total_zeros = CHROMA_FORMAT == CHROMA_420 ? x264_total_zeros_2x2_dc[i_total-1][i_total_zero]
                                                            : x264_total_zeros_2x4_dc[i_total-1][i_total_zero];
            bs_write_vlc( s, total_zeros );
        }
    }
    else if( (uint8_t)i_total < count_cat[ctx_block_cat] )
        bs_write_vlc( s, x264_total_zeros[i_total-1][i_total_zero] );

    int zero_run_code = x264_run_before[runlevel.mask];
    bs_write( s, zero_run_code&0x1f, zero_run_code>>5 );

    return i_total;
}

static const uint8_t ct_index[17] = {0,0,1,1,2,2,2,2,3,3,3,3,3,3,3,3,3};

#define x264_cavlc_block_residual(h,cat,idx,l)\
{\
    int nC = cat == DCT_CHROMA_DC ? 5 - CHROMA_V_SHIFT\
                                  : ct_index[x264_mb_predict_non_zero_code( h, cat == DCT_LUMA_DC ? (idx - LUMA_DC)*16 : idx )];\
    uint8_t *nnz = &h->mb.cache.non_zero_count[x264_scan8[idx]];\
    if( !*nnz )\
        bs_write_vlc( &h->out.bs, x264_coeff0_token[nC] );\
    else\
        *nnz = cavlc_block_residual_internal(h,cat,l,nC);\
}

static void cavlc_qp_delta( x264_t *h )
{
    bs_t *s = &h->out.bs;
    int i_dqp = h->mb.i_qp - h->mb.i_last_qp;

    /* Avoid writing a delta quant if we have an empty i16x16 block, e.g. in a completely
     * flat background area. Don't do this if it would raise the quantizer, since that could
     * cause unexpected deblocking artifacts. */
    if( h->mb.i_type == I_16x16 && !(h->mb.i_cbp_luma | h->mb.i_cbp_chroma)
        && !h->mb.cache.non_zero_count[x264_scan8[LUMA_DC]]
        && !h->mb.cache.non_zero_count[x264_scan8[CHROMA_DC+0]]
        && !h->mb.cache.non_zero_count[x264_scan8[CHROMA_DC+1]]
        && h->mb.i_qp > h->mb.i_last_qp )
    {
#if !RDO_SKIP_BS
        h->mb.i_qp = h->mb.i_last_qp;
#endif
        i_dqp = 0;
    }

    if( i_dqp )
    {
        if( i_dqp < -(QP_MAX_SPEC+1)/2 )
            i_dqp += QP_MAX_SPEC+1;
        else if( i_dqp > QP_MAX_SPEC/2 )
            i_dqp -= QP_MAX_SPEC+1;
    }
    bs_write_se( s, i_dqp );
}

static void cavlc_mvd( x264_t *h, int i_list, int idx, int width )
{
    bs_t *s = &h->out.bs;
    ALIGNED_4( int16_t mvp[2] );
    x264_mb_predict_mv( h, i_list, idx, width, mvp );
    bs_write_se( s, h->mb.cache.mv[i_list][x264_scan8[idx]][0] - mvp[0] );
    bs_write_se( s, h->mb.cache.mv[i_list][x264_scan8[idx]][1] - mvp[1] );
}

static inline void cavlc_8x8_mvd( x264_t *h, int i )
{
    switch( h->mb.i_sub_partition[i] )
    {
        case D_L0_8x8:
            cavlc_mvd( h, 0, 4*i, 2 );
            break;
        case D_L0_8x4:
            cavlc_mvd( h, 0, 4*i+0, 2 );
            cavlc_mvd( h, 0, 4*i+2, 2 );
            break;
        case D_L0_4x8:
            cavlc_mvd( h, 0, 4*i+0, 1 );
            cavlc_mvd( h, 0, 4*i+1, 1 );
            break;
        case D_L0_4x4:
            cavlc_mvd( h, 0, 4*i+0, 1 );
            cavlc_mvd( h, 0, 4*i+1, 1 );
            cavlc_mvd( h, 0, 4*i+2, 1 );
            cavlc_mvd( h, 0, 4*i+3, 1 );
            break;
    }
}

static ALWAYS_INLINE void cavlc_macroblock_luma_residual( x264_t *h, int plane_count )
{
    if( h->mb.b_transform_8x8 )
    {
        /* shuffle 8x8 dct coeffs into 4x4 lists */
        for( int p = 0; p < plane_count; p++ )
            for( int i8 = 0; i8 < 4; i8++ )
                if( h->mb.cache.non_zero_count[x264_scan8[p*16+i8*4]] )
                    h->zigzagf.interleave_8x8_cavlc( h->dct.luma4x4[p*16+i8*4], h->dct.luma8x8[p*4+i8],
                                                     &h->mb.cache.non_zero_count[x264_scan8[p*16+i8*4]] );
    }

    for( int p = 0; p < plane_count; p++ )
        FOREACH_BIT( i8, 0, h->mb.i_cbp_luma )
            for( int i4 = 0; i4 < 4; i4++ )
                x264_cavlc_block_residual( h, DCT_LUMA_4x4, i4+i8*4+p*16, h->dct.luma4x4[i4+i8*4+p*16] );
}

#if RDO_SKIP_BS
static ALWAYS_INLINE void cavlc_partition_luma_residual( x264_t *h, int i8, int p )
{
    if( h->mb.b_transform_8x8 && h->mb.cache.non_zero_count[x264_scan8[i8*4]] )
        h->zigzagf.interleave_8x8_cavlc( h->dct.luma4x4[i8*4+p*16], h->dct.luma8x8[i8+p*4],
                                         &h->mb.cache.non_zero_count[x264_scan8[i8*4+p*16]] );

    if( h->mb.i_cbp_luma & (1 << i8) )
        for( int i4 = 0; i4 < 4; i4++ )
            x264_cavlc_block_residual( h, DCT_LUMA_4x4, i4+i8*4+p*16, h->dct.luma4x4[i4+i8*4+p*16] );
}
#endif

static void cavlc_mb_header_i( x264_t *h, int i_mb_type, int i_mb_i_offset, int chroma )
{
	//h->mb.
    bs_t *s = &h->out.bs;
    if( i_mb_type == I_16x16 )
    {
		printf("Help");
		while (1);
        //bs_write_ue( s, i_mb_i_offset + 1 + x264_mb_pred_mode16x16_fix[h->mb.i_intra16x16_pred_mode] +
         //               h->mb.i_cbp_chroma * 4 + ( h->mb.i_cbp_luma == 0 ? 0 : 12 ) );
    }
    else //if( i_mb_type == I_4x4 || i_mb_type == I_8x8 )
    {
        int di = i_mb_type == I_8x8 ? 4 : 1;
		//check if all the same block type
		int type = x264_mb_pred_mode4x4_fix(h->mb.cache.intra4x4_pred_mode[x264_scan8[0]]);
		BOOL same = TRUE;
		for (int i = 0; i < 16; i += di)
		{
			if (!x264_mb_pred_mode4x4_fix(h->mb.cache.intra4x4_pred_mode[x264_scan8[i]]) == type)
			{
				same = FALSE;
				break;
			}
		}
		if (same)
		{
			//full block mode
			bs_write1(s, 0);

		}
		else
		{
			//sub block mode
			bs_write1(s, 1);

		}


        /*bs_write_ue( s, i_mb_i_offset + 0 );
        if( h->pps->b_transform_8x8_mode )
            bs_write1( s, h->mb.b_transform_8x8 );*/

        /* Prediction: Luma */
        for( int i = 0; i < 16; i += di )
        {
            int i_pred = x264_mb_predict_intra4x4_mode( h, i );
            int i_mode = x264_mb_pred_mode4x4_fix( h->mb.cache.intra4x4_pred_mode[x264_scan8[i]] );

            if( i_pred == i_mode )
                bs_write1( s, 1 );  /* b_prev_intra4x4_pred_mode */
            else
                bs_write( s, 4, i_mode - (i_mode > i_pred) );
        }

    }
    if( chroma )
        bs_write_ue( s, x264_mb_chroma_pred_mode_fix[h->mb.i_chroma_pred_mode] );
}

static ALWAYS_INLINE void cavlc_mb_header_p( x264_t *h, int i_mb_type, int chroma )
{
    bs_t *s = &h->out.bs;
    if( i_mb_type == P_L0 )
    {
        if( h->mb.i_partition == D_16x16 )
        {
            bs_write1( s, 1 );

            if( h->mb.pic.i_fref[0] > 1 )
                bs_write_te( s, h->mb.pic.i_fref[0] - 1, h->mb.cache.ref[0][x264_scan8[0]] );
            cavlc_mvd( h, 0, 0, 4 );
        }
        else if( h->mb.i_partition == D_16x8 )
        {
            bs_write_ue( s, 1 );
            if( h->mb.pic.i_fref[0] > 1 )
            {
                bs_write_te( s, h->mb.pic.i_fref[0] - 1, h->mb.cache.ref[0][x264_scan8[0]] );
                bs_write_te( s, h->mb.pic.i_fref[0] - 1, h->mb.cache.ref[0][x264_scan8[8]] );
            }
            cavlc_mvd( h, 0, 0, 4 );
            cavlc_mvd( h, 0, 8, 4 );
        }
        else if( h->mb.i_partition == D_8x16 )
        {
            bs_write_ue( s, 2 );
            if( h->mb.pic.i_fref[0] > 1 )
            {
                bs_write_te( s, h->mb.pic.i_fref[0] - 1, h->mb.cache.ref[0][x264_scan8[0]] );
                bs_write_te( s, h->mb.pic.i_fref[0] - 1, h->mb.cache.ref[0][x264_scan8[4]] );
            }
            cavlc_mvd( h, 0, 0, 2 );
            cavlc_mvd( h, 0, 4, 2 );
        }
    }
    else if( i_mb_type == P_8x8 )
    {
        int b_sub_ref;
        if( (h->mb.cache.ref[0][x264_scan8[0]] | h->mb.cache.ref[0][x264_scan8[ 4]] |
             h->mb.cache.ref[0][x264_scan8[8]] | h->mb.cache.ref[0][x264_scan8[12]]) == 0 )
        {
            bs_write_ue( s, 4 );
            b_sub_ref = 0;
        }
        else
        {
            bs_write_ue( s, 3 );
            b_sub_ref = 1;
        }

        /* sub mb type */
        if( h->param.analyse.inter & X264_ANALYSE_PSUB8x8 )
            for( int i = 0; i < 4; i++ )
                bs_write_ue( s, subpartition_p_to_golomb[ h->mb.i_sub_partition[i] ] );
        else
            bs_write( s, 4, 0xf );

        /* ref0 */
        if( b_sub_ref )
        {
            bs_write_te( s, h->mb.pic.i_fref[0] - 1, h->mb.cache.ref[0][x264_scan8[0]] );
            bs_write_te( s, h->mb.pic.i_fref[0] - 1, h->mb.cache.ref[0][x264_scan8[4]] );
            bs_write_te( s, h->mb.pic.i_fref[0] - 1, h->mb.cache.ref[0][x264_scan8[8]] );
            bs_write_te( s, h->mb.pic.i_fref[0] - 1, h->mb.cache.ref[0][x264_scan8[12]] );
        }

        for( int i = 0; i < 4; i++ )
            cavlc_8x8_mvd( h, i );
    }
    else //if( IS_INTRA( i_mb_type ) )
        cavlc_mb_header_i( h, i_mb_type, 5, chroma );
}

static ALWAYS_INLINE void cavlc_mb_header_b( x264_t *h, int i_mb_type, int chroma )
{
    bs_t *s = &h->out.bs;
    if( i_mb_type == B_8x8 )
    {
        bs_write_ue( s, 22 );

        /* sub mb type */
        for( int i = 0; i < 4; i++ )
            bs_write_ue( s, subpartition_b_to_golomb[ h->mb.i_sub_partition[i] ] );

        /* ref */
        if( h->mb.pic.i_fref[0] > 1 )
            for( int i = 0; i < 4; i++ )
                if( x264_mb_partition_listX_table[0][ h->mb.i_sub_partition[i] ] )
                    bs_write_te( s, h->mb.pic.i_fref[0] - 1, h->mb.cache.ref[0][x264_scan8[i*4]] );
        if( h->mb.pic.i_fref[1] > 1 )
            for( int i = 0; i < 4; i++ )
                if( x264_mb_partition_listX_table[1][ h->mb.i_sub_partition[i] ] )
                    bs_write_te( s, h->mb.pic.i_fref[1] - 1, h->mb.cache.ref[1][x264_scan8[i*4]] );

        /* mvd */
        for( int i = 0; i < 4; i++ )
            if( x264_mb_partition_listX_table[0][ h->mb.i_sub_partition[i] ] )
                cavlc_mvd( h, 0, 4*i, 2 );
        for( int i = 0; i < 4; i++ )
            if( x264_mb_partition_listX_table[1][ h->mb.i_sub_partition[i] ] )
                cavlc_mvd( h, 1, 4*i, 2 );
    }
    else if( i_mb_type >= B_L0_L0 && i_mb_type <= B_BI_BI )
    {
        /* All B mode */
        /* Motion Vector */
        const uint8_t (*b_list)[2] = x264_mb_type_list_table[i_mb_type];
        const int i_ref0_max = h->mb.pic.i_fref[0] - 1;
        const int i_ref1_max = h->mb.pic.i_fref[1] - 1;

        bs_write_ue( s, mb_type_b_to_golomb[ h->mb.i_partition - D_16x8 ][ i_mb_type - B_L0_L0 ] );
        if( h->mb.i_partition == D_16x16 )
        {
            if( i_ref0_max && b_list[0][0] ) bs_write_te( s, i_ref0_max, h->mb.cache.ref[0][x264_scan8[0]] );
            if( i_ref1_max && b_list[1][0] ) bs_write_te( s, i_ref1_max, h->mb.cache.ref[1][x264_scan8[0]] );
            if( b_list[0][0] ) cavlc_mvd( h, 0, 0, 4 );
            if( b_list[1][0] ) cavlc_mvd( h, 1, 0, 4 );
        }
        else
        {
            if( i_ref0_max && b_list[0][0] ) bs_write_te( s, i_ref0_max, h->mb.cache.ref[0][x264_scan8[ 0]] );
            if( i_ref0_max && b_list[0][1] ) bs_write_te( s, i_ref0_max, h->mb.cache.ref[0][x264_scan8[12]] );
            if( i_ref1_max && b_list[1][0] ) bs_write_te( s, i_ref1_max, h->mb.cache.ref[1][x264_scan8[ 0]] );
            if( i_ref1_max && b_list[1][1] ) bs_write_te( s, i_ref1_max, h->mb.cache.ref[1][x264_scan8[12]] );
            if( h->mb.i_partition == D_16x8 )
            {
                if( b_list[0][0] ) cavlc_mvd( h, 0, 0, 4 );
                if( b_list[0][1] ) cavlc_mvd( h, 0, 8, 4 );
                if( b_list[1][0] ) cavlc_mvd( h, 1, 0, 4 );
                if( b_list[1][1] ) cavlc_mvd( h, 1, 8, 4 );
            }
            else //if( h->mb.i_partition == D_8x16 )
            {
                if( b_list[0][0] ) cavlc_mvd( h, 0, 0, 2 );
                if( b_list[0][1] ) cavlc_mvd( h, 0, 4, 2 );
                if( b_list[1][0] ) cavlc_mvd( h, 1, 0, 2 );
                if( b_list[1][1] ) cavlc_mvd( h, 1, 4, 2 );
            }
        }
    }
    else if( i_mb_type == B_DIRECT )
        bs_write1( s, 1 );
    else //if( IS_INTRA( i_mb_type ) )
        cavlc_mb_header_i( h, i_mb_type, 23, chroma );
}

static int encode_dct(x264_t* h, dctcoef *l, int length)
{
	const int table = 0;
	bs_t *s = &h->out.bs;
	const uint16_t* r11A = table == 1 ? vx2_table1_a : vx2_table0_a;
	const uint8_t* r11B = table == 1 ? vx2_table1_b : vx2_table0_b;
	const int (*reftable)[64][2] = table == 1 ? vx2_table1_a_rev : vx2_table0_a_rev;
	int lastnonzero = 0;
	int nnz = 0;
	for (int i = 0; i < length; i++)
	{
		if (l[i] != 0)
		{
			lastnonzero = i;
			nnz++;
		}
	}
	int skip = 0;
	for (int i = 0; i < length; i++)
	{
		if (l[i] == 0 && lastnonzero != 0)
		{
			skip++;
			continue;
		}
		int val = l[i];
		if (val < 0) 
			val = -val;
		if (val <= 31)
		{
			int idx = reftable[val][skip][(i == lastnonzero) ? 1 : 0];
			if (idx >= 0)
			{
				int nrbits = r11A[idx] & 0xF;
				uint32_t tidx = (uint32_t)idx;
				if (nrbits < 12)
					tidx >>= (12 - nrbits);
				else if (nrbits > 12)
					tidx <<= (nrbits - 12);
				if (l[i] < 0) 
					tidx |= 1;
				bs_write(s, nrbits, tidx);
				skip = 0;
				goto end;
			}
			int newskip = skip - r11B[(val | (((i == lastnonzero) ? 1 : 0) << 6)) + 0x80];
			if (newskip >= 0)
			{
				idx = reftable[val][newskip][(i == lastnonzero) ? 1 : 0];
				if (idx >= 0)
				{
					bs_write(s, 7, 3);
					bs_write1(s, 1);
					bs_write1(s, 0);
					int nrbits = r11A[idx] & 0xF;
					uint32_t tidx = (uint32_t)idx;
					if (nrbits < 12)
						tidx >>= (12 - nrbits);
					else if (nrbits > 12)
						tidx <<= (nrbits - 12);
					if (l[i] < 0)
						tidx |= 1;
					bs_write(s, nrbits, tidx);
					skip = 0;
					goto end;
				}
			}
		}
		int newval = val - r11B[skip | (((i == lastnonzero) ? 1 : 0) << 6)];
		if (newval >= 0 && newval <= 31)
		{
			int idx = reftable[newval][skip][(i == lastnonzero) ? 1 : 0];
			if (idx >= 0)
			{
				bs_write(s, 7, 3);
				bs_write1(s, 0);
				int nrbits = r11A[idx] & 0xF;
				uint32_t tidx = (uint32_t)idx;
				if (nrbits < 12)
					tidx >>= (12 - nrbits);
				else if (nrbits > 12)
					tidx <<= (nrbits - 12);
				if (l[i] < 0) 
					tidx |= 1;
				bs_write(s, nrbits, tidx);
				skip = 0;
				goto end;
			}
		}
		//This is easiest way of writing the DCT, but also costs the most bits
		bs_write(s, 7, 3);
		bs_write1(s, 1);
		bs_write1(s, 1);
		if (i == lastnonzero)
			bs_write1(s, 1);
		else
			bs_write1(s, 0);
		bs_write(s, 6, skip);
		skip = 0;
		bs_write(s, 12, l[i]);
	end:
		if (i == lastnonzero) 
			break;
	}
	return nnz;
}

static uint8_t block_mask_to_golomb_table[] =
{
	0, 7, 6, 12, 5, 19, 29, 13, 4, 27, 17, 8, 14, 11, 9, 3, 20, 33, 34, 24, 35, 30, 41, 15, 36, 40, 31, 10, 28, 16, 18, 1, 37, 55, 57, 52, 58, 56, 63, 46, 61, 62, 60, 48, 59, 49, 54, 21, 43, 44, 45, 32, 47, 39, 53, 22, 51, 50, 42, 23, 38, 25, 26, 2,
};

static uint8_t subblock_mask_to_golomb_table[] =
{
	2, 4, 3, 8, 5, 14, 16, 12, 6, 15, 13, 9, 7, 10, 11, 1
};

static void encode_i_block(x264_t *h)
{
	bs_t *s = &h->out.bs;
	const int i_mb_type = h->mb.i_type;
	const int i_mb_pos_start = bs_pos(s);

	int di = i_mb_type == I_8x8 ? 4 : 1;

	//check if prediction modes are all equal
	BOOL equalPredict = TRUE;
	int equalMode = x264_mb_pred_mode4x4_fix(h->mb.cache.intra4x4_pred_mode[x264_scan8[0]]);
	for (int i = di; i < 16; i += di)
	{
		int mode = x264_mb_pred_mode4x4_fix(h->mb.cache.intra4x4_pred_mode[x264_scan8[i]]);
		if (mode != equalMode)
		{
			equalPredict = FALSE;
			break;
		}
	}
	if (h->sh.i_type == SLICE_TYPE_I)
	{
		bs_write1(s, !equalPredict);
		h->stat.frame.i_mv_bits++;
	}
	else
	{
		if (equalPredict)
			bs_write(s, 5, 0xE >> 1);
		else
			bs_write(s, 5, 0x18 >> 1);
		h->stat.frame.i_mv_bits += 5;
	}

	//which blocks are actually coded
#if !RDO_SKIP_BS
	int tmp = bs_pos(s);
#endif
	uint8_t mask =
		(!!h->mb.cache.non_zero_count[x264_scan8[0 * 4]]) |
		((!!h->mb.cache.non_zero_count[x264_scan8[1 * 4]]) << 1) |
		((!!h->mb.cache.non_zero_count[x264_scan8[2 * 4]]) << 2) |
		((!!h->mb.cache.non_zero_count[x264_scan8[3 * 4]]) << 3);
	bs_write_ue(s, block_mask_to_golomb_table[(!!h->mb.cache.non_zero_count[x264_scan8[16 + 1 * 16]] << 5) | (!!h->mb.cache.non_zero_count[x264_scan8[16 + 0 * 16]] << 4) | (i_mb_type == I_8x8 ? mask : 0xF)]);
#if !RDO_SKIP_BS
	h->stat.frame.i_tex_bits += bs_pos(s) - tmp;
#endif

	if (equalPredict)
	{
		bs_write(s, 3, equalMode);
		h->stat.frame.i_mv_bits += 3;
	}

	if (h->mb.b_transform_8x8)
	{
		for (int i8 = 0; i8 < 4; i8++)
		{
#if !RDO_SKIP_BS
			tmp = bs_pos(s);
#endif
			if (h->mb.cache.non_zero_count[x264_scan8[i8 * 4]])
				bs_write1(s, 1);//don't subdivide into 4x4

			if (!equalPredict)
			{
				//intra predictor prediction
				int i_pred = x264_mb_predict_intra4x4_mode(h, i8 * 4);
				int i_mode = x264_mb_pred_mode4x4_fix(h->mb.cache.intra4x4_pred_mode[x264_scan8[i8 * 4]]);

				if (i_pred == i_mode)
					bs_write1(s, 1);  /* b_prev_intra4x4_pred_mode */
				else
					bs_write(s, 4, i_mode - (i_mode - 1 >= i_pred));
			}

			//todo: write plane param here when implemented and mode == 2
#if !RDO_SKIP_BS
			h->stat.frame.i_mv_bits += bs_pos(s) - tmp;
#endif
			if (h->mb.cache.non_zero_count[x264_scan8[i8 * 4]])
			{
#if !RDO_SKIP_BS
				tmp = bs_pos(s);
#endif			
				//if (h->mb.cache.non_zero_count[x264_scan8[i8 * 4]])
				//{
					h->mb.cache.non_zero_count[x264_scan8[i8 * 4]] = encode_dct(h, h->dct.luma8x8[i8], 64);
				//}
				/*else
				{
					dctcoef zero[64] = { 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 };
					encode_dct(h, zero, 64);
				}*/

#if !RDO_SKIP_BS
				h->stat.frame.i_tex_bits += bs_pos(s) - tmp;
#endif
			}
		}
	}
	else
	{
		for (int i8 = 0; i8 < 4; i8++)
		{
#if !RDO_SKIP_BS
			tmp = bs_pos(s);
#endif
			uint8_t mask =
				(!!h->mb.cache.non_zero_count[x264_scan8[i8 * 4 + 0]]) |
				((!!h->mb.cache.non_zero_count[x264_scan8[i8 * 4 + 1]]) << 1) |
				((!!h->mb.cache.non_zero_count[x264_scan8[i8 * 4 + 2]]) << 2) |
				((!!h->mb.cache.non_zero_count[x264_scan8[i8 * 4 + 3]]) << 3);
			bs_write_ue(s, subblock_mask_to_golomb_table[mask]);
#if !RDO_SKIP_BS
			h->stat.frame.i_tex_bits += bs_pos(s) - tmp;
#endif
			for (int i4 = 0; i4 < 4; i4++)
			{				
#if !RDO_SKIP_BS
				tmp = bs_pos(s);
#endif
				if (!equalPredict)
				{
					//intra predictor prediction
					int i_pred = x264_mb_predict_intra4x4_mode(h, i8 * 4 + i4);
					int i_mode = x264_mb_pred_mode4x4_fix(h->mb.cache.intra4x4_pred_mode[x264_scan8[i8 * 4 + i4]]);

					if (i_pred == i_mode)
						bs_write1(s, 1);  /* b_prev_intra4x4_pred_mode */
					else
						bs_write(s, 4, i_mode - (i_mode > i_pred));
				}

#if !RDO_SKIP_BS
				h->stat.frame.i_mv_bits += bs_pos(s) - tmp;
#endif	

				//todo: write plane param here when implemented and mode == 2
				if (h->mb.cache.non_zero_count[x264_scan8[i8 * 4 + i4]])
				{
#if !RDO_SKIP_BS
					tmp = bs_pos(s);
#endif			
						h->mb.cache.non_zero_count[x264_scan8[i8 * 4 + i4]] = encode_dct(h, h->dct.luma4x4[i8 * 4 + i4], 16);
#if !RDO_SKIP_BS
					h->stat.frame.i_tex_bits += bs_pos(s) - tmp;
#endif
				}
			}
		}
	}

	//chroma prediction mode
#if !RDO_SKIP_BS
	tmp = bs_pos(s);
#endif
	bs_write(s, 3, x264_mb_chroma_pred_mode_fix[h->mb.i_chroma_pred_mode]);
	//todo: write plane params here when implemented and mode == 2
#if !RDO_SKIP_BS
	h->stat.frame.i_mv_bits += bs_pos(s) - tmp;
#endif		
	for (int i = 0; i < 2; i++)
	{
		if (h->mb.cache.non_zero_count[x264_scan8[16 + i * 16]])
		{
			bs_write1(s, 1);//don't subdivide into 4x4
			h->stat.frame.i_mv_bits++;
#if !RDO_SKIP_BS
				tmp = bs_pos(s);
#endif			
				h->mb.cache.non_zero_count[x264_scan8[16 + i * 16]] = encode_dct(h, h->dct.luma8x8[4 + 4 * i], 64);
#if !RDO_SKIP_BS
				h->stat.frame.i_tex_bits += bs_pos(s) - tmp;
#endif
		}
	}
}

static const int SizeToIdx[17] =
{
	-1, -1, 0, -1, 1, -1, -1, -1, 2, -1, -1, -1, -1, -1, -1, -1, 3
};

static const int HuffEncodeValTable[4][4][10] =
{
	{
		{ 0 >> 1, 6 >> 1, 5, 4, 2, 3, -1, -1, -1, -1 },
		{ 0 >> 2, 12 >> 2, 10 >> 1, 6 >> 1, 4 >> 1, 9, -1, -1, 8, -1 },
		{ 12 >> 1, 0 >> 3, 10 >> 1, 15, 14, 9, -1, -1, 8, -1 },
		{ 14 >> 1, 0 >> 3, 10 >> 1, 13, 9, 8, -1, -1, 12, -1 }
	},
	{
		{ 0 >> 2, 12 >> 2, 10 >> 1, 6 >> 1, 9, 4 >> 1, -1, -1, -1, 8 },
		{ 0 >> 2, 12 >> 2, 10 >> 1, 4 >> 1, 9, 8, -1, -1, 7, 6 },
		{ 20 >> 2, 0 >> 4, 16 >> 2, 28 >> 1, 31, 30, -1, -1, 26 >> 1, 24 >> 1 },
		{ 0 >> 2, 12 >> 2, 6 >> 1, 10, 5, 4, -1, -1, 11, 8 >> 1 }
	},
	{
		{ 12 >> 1, 0 >> 3, 10 >> 1, 15, 14, 9, -1, -1, -1, 8 },
		{ 20 >> 2, 0 >> 4, 16 >> 2, 28 >> 1, 31, 30, -1, -1, 26 >> 1, 24 >> 1 },
		{ 10 >> 1, 12 >> 2, 4 >> 1, 0 >> 1, 3, 2, -1, -1, 8 >> 1, 6 >> 1 },
		{ 28 >> 2, 16 >> 3, 8 >> 2, 12 >> 1, 15, 14, -1, -1, 24 >> 2, 0 >> 3 }
	},
	{
		{ 12 >> 1, 0 >> 3, 10 >> 1, 15, 9, 8, -1, -1, -1, 14 },
		{ 0 >> 2, 12 >> 2, 6 >> 1, 10, 5, 4, -1, -1, 8 >> 1, 11 },
		{ 20 >> 2, 24 >> 3, 0 >> 2, 16 >> 1, 19, 18, -1, -1, 8 >> 3, 4 >> 2 },
		{ 1, 16 >> 3, 8 >> 2, 12 >> 1, 27, 26, 14 >> 1, 24 >> 1, 0 >> 3, 28 >> 2 }
	}
};

static const int HuffEncodeBitTable[4][4][10] =
{
	{
		{ 2, 2, 3, 3, 3, 3, -1, -1, -1, -1 },
		{ 2, 2, 3, 3, 3, 4, -1, -1, 4, -1 },
		{ 3, 1, 3, 4, 4, 4, -1, -1, 4, -1 },
		{ 3, 1, 3, 4, 4, 4, -1, -1, 4, -1 }
	},
	{
		{ 2, 2, 3, 3, 4, 3, -1, -1, -1, 4 },
		{ 2, 2, 3, 3, 4, 4, -1, -1, 4, 4 },
		{ 3, 1, 3, 4, 5, 5, -1, -1, 4, 4 },
		{ 2, 2, 3, 4, 4, 4, -1, -1, 4, 3 }
	},
	{
		{ 3, 1, 3, 4, 4, 4, -1, -1, -1, 4 },
		{ 3, 1, 3, 4, 5, 5, -1, -1, 4, 4 },
		{ 3, 2, 3, 3, 4, 4, -1, -1, 3, 3 },
		{ 3, 2, 3, 4, 5, 5, -1, -1, 3, 2 }
	},
	{
		{ 3, 1, 3, 4, 4, 4, -1, -1, -1, 4 },
		{ 2, 2, 3, 4, 4, 4, -1, -1, 3, 4 },
		{ 3, 2, 3, 4, 5, 5, -1, -1, 2, 3 },
		{ 1, 3, 4, 5, 6, 6, 5, 5, 3, 4 }
	}
};

#define mobi_encode_p_partition_mode(s, w, h, mode)	bs_write((s), HuffEncodeBitTable[SizeToIdx[(w)]][SizeToIdx[(h)]][(mode)], HuffEncodeValTable[SizeToIdx[(w)]][SizeToIdx[(h)]][(mode)])

static void mobi_encode_p_partition(x264_t *h, int idx, int width, int height, int px, int py, int* lastMv)
{
	int idx44 = ((idx >> 1) & 1) | (((idx >> 4) & 1) << 1);
	bs_t *s = &h->out.bs;
	if (width == 16 && height == 16 && (h->mb.i_partition == D_16x8 || h->mb.i_type == P_8x8))
	{
		mobi_encode_p_partition_mode(s, 16, 16, MOBI_P_PART_H_SPLIT);
		mobi_encode_p_partition(h, 0, 16, 8, px, py, NULL);
		mobi_encode_p_partition(h, 2 * 8, 16, 8, px, py, lastMv);
	}
	else if (width == 16 && height == 16 && h->mb.i_partition == D_8x16)
	{
		mobi_encode_p_partition_mode(s, 16, 16, MOBI_P_PART_V_SPLIT);
		mobi_encode_p_partition(h, 0, 8, 16, px, py, NULL);
		mobi_encode_p_partition(h, 2, 8, 16, px, py, lastMv);
	}
	else if (width == 16 && height == 8 && h->mb.i_partition == D_8x8)
	{
		mobi_encode_p_partition_mode(s, 16, 8, MOBI_P_PART_V_SPLIT);
		mobi_encode_p_partition(h, idx, 8, 8, px, py, NULL);
		mobi_encode_p_partition(h, idx + 2, 8, 8, px, py, lastMv);
	}
	else if (width == 8 && height == 8 && (h->mb.i_sub_partition[idx44] == D_L0_8x4 || h->mb.i_sub_partition[idx44] == D_L0_4x4))
	{
		mobi_encode_p_partition_mode(s, 8, 8, MOBI_P_PART_H_SPLIT);
		mobi_encode_p_partition(h, idx, 8, 4, px, py, NULL);
		mobi_encode_p_partition(h, idx + 8, 8, 4, px, py, lastMv);
	}
	else if (width == 8 && height == 8 && h->mb.i_sub_partition[idx44] == D_L0_4x8)
	{
		mobi_encode_p_partition_mode(s, 8, 8, MOBI_P_PART_V_SPLIT);
		mobi_encode_p_partition(h, idx, 4, 8, px, py, NULL);
		mobi_encode_p_partition(h, idx + 1, 4, 8, px, py, lastMv);
	}
	else if (width == 8 && height == 4 && h->mb.i_sub_partition[idx44] == D_L0_4x4)
	{
		mobi_encode_p_partition_mode(s, 8, 4, MOBI_P_PART_V_SPLIT);
		mobi_encode_p_partition(h, idx, 4, 4, px, py, NULL);
		mobi_encode_p_partition(h, idx + 1, 4, 4, px, py, lastMv);
	}
	else
	{
		int ref = h->mb.cache.ref[0][x264_scan8[0] + idx];
		int mvx = h->mb.cache.mv[0][x264_scan8[0] + idx][0] >> 1;
		int mvy = h->mb.cache.mv[0][x264_scan8[0] + idx][1] >> 1;
		int dx = mvx - px;
		int dy = mvy - py;
		if (ref == 0 && dx == 0 && dy == 0)
			mobi_encode_p_partition_mode(s, width, height, MOBI_P_PART_FRAME0_DELTA0);
		else
		{
			switch (ref)
			{
				case 0:
					mobi_encode_p_partition_mode(s, width, height, MOBI_P_PART_FRAME0);
					break;
				case 1:
					mobi_encode_p_partition_mode(s, width, height, MOBI_P_PART_FRAME1);
					break;
				case 2:
					mobi_encode_p_partition_mode(s, width, height, MOBI_P_PART_FRAME2);
					break;
				case 3:
					mobi_encode_p_partition_mode(s, width, height, MOBI_P_PART_FRAME3);
					break;
				case 4:
					mobi_encode_p_partition_mode(s, width, height, MOBI_P_PART_FRAME4);
					break;
				default:
					printf("Invalid reference (%d)!", ref);
					while (1);
					break;
			}
			bs_write_se(s, dx);
			bs_write_se(s, dy);
		}
		if (lastMv)
		{
			lastMv[0] = mvx;
			lastMv[1] = mvy;
		}
	}
}

static const uint8_t REV_byte_116160[] =
{
	0, 3, 5, 7, 2, 8, 16, 11, 4, 15, 9, 13, 6, 10, 12, 1,
	17, 28, 27, 24, 29, 30, 33, 20, 25, 34, 26, 22, 23, 21,
	19, 14, 31, 42, 44, 46, 43, 51, 61, 49, 45, 60, 55, 53,
	47, 50, 54, 32, 48, 56, 59, 40, 57, 41, 63, 35, 58, 62,
	52, 38, 39, 36, 37, 18
};

static const uint8_t REV_byte_1165C4[] =
{
	0, 2, 4, 6, 1, 7, 15, 10, 3, 14, 8, 13, 5, 11, 12, 9,
};

static void encode_p_block(x264_t *h)
{
	bs_t *s = &h->out.bs;
	if (h->mb.i_type == P_L0 || h->mb.i_type == P_8x8)
	{
		int16_t mv[2];
		x264_mb_predict_mv(h, 0, 0, 0, mv);
		mv[0] >>= 1;
		mv[1] >>= 1;
#if !RDO_SKIP_BS
		int tmp = bs_pos(s);
#endif
		int lastMv[2];
		mobi_encode_p_partition(h, 0, 16, 16, mv[0], mv[1], lastMv);
#if !RDO_SKIP_BS
		h->stat.frame.i_mv_bits += bs_pos(s) - tmp;
#endif
		//which blocks are actually coded
#if !RDO_SKIP_BS
		tmp = bs_pos(s);
#endif
		BOOL use8x8 = x264_mb_transform_8x8_allowed(h) && h->mb.b_transform_8x8;
		uint8_t mask =
			(!!h->mb.cache.non_zero_count[x264_scan8[0 * 4]]) |
			((!!h->mb.cache.non_zero_count[x264_scan8[1 * 4]]) << 1) |
			((!!h->mb.cache.non_zero_count[x264_scan8[2 * 4]]) << 2) |
			((!!h->mb.cache.non_zero_count[x264_scan8[3 * 4]]) << 3);
		uint8_t masks[] =
		{
			(!!h->mb.cache.non_zero_count[x264_scan8[0 * 4 + 0]]) |
			((!!h->mb.cache.non_zero_count[x264_scan8[0 * 4 + 1]]) << 1) |
			((!!h->mb.cache.non_zero_count[x264_scan8[0 * 4 + 2]]) << 2) |
			((!!h->mb.cache.non_zero_count[x264_scan8[0 * 4 + 3]]) << 3),
			(!!h->mb.cache.non_zero_count[x264_scan8[1 * 4 + 0]]) |
			((!!h->mb.cache.non_zero_count[x264_scan8[1 * 4 + 1]]) << 1) |
			((!!h->mb.cache.non_zero_count[x264_scan8[1 * 4 + 2]]) << 2) |
			((!!h->mb.cache.non_zero_count[x264_scan8[1 * 4 + 3]]) << 3),
			(!!h->mb.cache.non_zero_count[x264_scan8[2 * 4 + 0]]) |
			((!!h->mb.cache.non_zero_count[x264_scan8[2 * 4 + 1]]) << 1) |
			((!!h->mb.cache.non_zero_count[x264_scan8[2 * 4 + 2]]) << 2) |
			((!!h->mb.cache.non_zero_count[x264_scan8[2 * 4 + 3]]) << 3),
			(!!h->mb.cache.non_zero_count[x264_scan8[3 * 4 + 0]]) |
			((!!h->mb.cache.non_zero_count[x264_scan8[3 * 4 + 1]]) << 1) |
			((!!h->mb.cache.non_zero_count[x264_scan8[3 * 4 + 2]]) << 2) |
			((!!h->mb.cache.non_zero_count[x264_scan8[3 * 4 + 3]]) << 3)
		};
		uint8_t mask4x4 = (!!masks[0]) | (!!masks[1] << 1) | (!!masks[2] << 2) | (!!masks[3] << 3);
		bs_write_ue(s, REV_byte_116160[(!!h->mb.cache.non_zero_count[x264_scan8[16 + 1 * 16]] << 5) | (!!h->mb.cache.non_zero_count[x264_scan8[16 + 0 * 16]] << 4) | (use8x8 ? mask : mask4x4)]);
#if !RDO_SKIP_BS
		h->stat.frame.i_tex_bits += bs_pos(s) - tmp;
#endif
		
		if (use8x8)
		{
			for (int i8 = 0; i8 < 4; i8++)
			{
				if (h->mb.cache.non_zero_count[x264_scan8[i8 * 4]])
				{
					bs_write1(s, 1);//don't subdivide into 4x4
					h->stat.frame.i_mv_bits++;
#if !RDO_SKIP_BS
					int tmp = bs_pos(s);
#endif			
					h->mb.cache.non_zero_count[x264_scan8[i8 * 4]] = encode_dct(h, h->dct.luma8x8[i8], 64);
#if !RDO_SKIP_BS
					h->stat.frame.i_tex_bits += bs_pos(s) - tmp;
#endif
				}
			}
		}
		else
		{
			for (int i8 = 0; i8 < 4; i8++)
			{
				if (!((mask4x4 >> i8) & 1))
					continue;
#if !RDO_SKIP_BS
				int tmp = bs_pos(s);
#endif
				bs_write_ue(s, REV_byte_1165C4[masks[i8]]);
#if !RDO_SKIP_BS
				h->stat.frame.i_tex_bits += bs_pos(s) - tmp;
#endif
				for (int i4 = 0; i4 < 4; i4++)
				{
					if (h->mb.cache.non_zero_count[x264_scan8[i8 * 4 + i4]])
					{
#if !RDO_SKIP_BS
						tmp = bs_pos(s);
#endif			
						h->mb.cache.non_zero_count[x264_scan8[i8 * 4 + i4]] = encode_dct(h, h->dct.luma4x4[i8 * 4 + i4], 16);
#if !RDO_SKIP_BS
						h->stat.frame.i_tex_bits += bs_pos(s) - tmp;
#endif
					}
				}
			}
		}
	
		for (int i = 0; i < 2; i++)
		{
			if (h->mb.cache.non_zero_count[x264_scan8[16 + i * 16]])
			{
				bs_write1(s, 1);//don't subdivide into 4x4
				h->stat.frame.i_mv_bits++;
#if !RDO_SKIP_BS
				int tmp = bs_pos(s);
#endif			
				h->mb.cache.non_zero_count[x264_scan8[16 + i * 16]] = encode_dct(h, h->dct.luma8x8[4 + 4 * i], 64);
#if !RDO_SKIP_BS
				h->stat.frame.i_tex_bits += bs_pos(s) - tmp;
#endif
			}
		}
	}
	else //if( IS_INTRA( i_mb_type ) )
		encode_i_block(h);
}

/*****************************************************************************
 * x264_macroblock_write:
 *****************************************************************************/
void x264_macroblock_write_cavlc( x264_t *h )
{
    bs_t *s = &h->out.bs;
    const int i_mb_type = h->mb.i_type;
    int plane_count = CHROMA444 ? 3 : 1;
    int chroma = !CHROMA444;
#if RDO_SKIP_BS
    s->i_bits_encoded = 0;
#else
    const int i_mb_pos_start = bs_pos( s );
    int       i_mb_pos_tex;
#endif

#if !RDO_SKIP_BS
    /*if( i_mb_type == I_PCM )
    {
        static const uint8_t i_offsets[3] = {5,23,0};
        uint8_t *p_start = s->p_start;
        bs_write_ue( s, i_offsets[h->sh.i_type] + 25 );
        i_mb_pos_tex = bs_pos( s );
        h->stat.frame.i_mv_bits += i_mb_pos_tex - i_mb_pos_start;

        bs_align_0( s );

        for( int p = 0; p < plane_count; p++ )
            for( int i = 0; i < 256; i++ )
                bs_write( s, BIT_DEPTH, h->mb.pic.p_fenc[p][i] );
        if( chroma )
            for( int ch = 1; ch < 3; ch++ )
                for( int i = 0; i < 16>>CHROMA_V_SHIFT; i++ )
                    for( int j = 0; j < 8; j++ )
                        bs_write( s, BIT_DEPTH, h->mb.pic.p_fenc[ch][i*FENC_STRIDE+j] );

        bs_init( s, s->p, s->p_end - s->p );
        s->p_start = p_start;

        h->stat.frame.i_tex_bits += bs_pos(s) - i_mb_pos_tex;
        return;
    }*/
#endif
	if (h->sh.i_type == SLICE_TYPE_P)
		encode_p_block(h);
	else //if (h->sh.i_type == SLICE_TYPE_I)
		encode_i_block(h);
}

#if RDO_SKIP_BS
/*****************************************************************************
 * RD only; doesn't generate a valid bitstream
 * doesn't write cbp or chroma dc (I don't know how much this matters)
 * doesn't write ref (never varies between calls, so no point in doing so)
 * only writes subpartition for p8x8, needed for sub-8x8 mode decision RDO
 * works on all partition sizes except 16x16
 *****************************************************************************/
static int partition_size_cavlc( x264_t *h, int i8, int i_pixel )
{
    bs_t *s = &h->out.bs;
    const int i_mb_type = h->mb.i_type;
    int b_8x16 = h->mb.i_partition == D_8x16;
    int plane_count = CHROMA444 ? 3 : 1;
    int j;

    h->out.bs.i_bits_encoded = 0;

    if( i_mb_type == P_8x8 )
    {
        cavlc_8x8_mvd( h, i8 );
        bs_write_ue( s, subpartition_p_to_golomb[ h->mb.i_sub_partition[i8] ] );
    }
    else if( i_mb_type == P_L0 )
        cavlc_mvd( h, 0, 4*i8, 4>>b_8x16 );

    for( j = (i_pixel < PIXEL_8x8); j >= 0; j-- )
    {
        for( int p = 0; p < plane_count; p++ )
            cavlc_partition_luma_residual( h, i8, p );
        if( h->mb.i_cbp_chroma )
        {
            if( CHROMA_FORMAT == CHROMA_422 )
            {
                int offset = (5*i8) & 0x09;
                x264_cavlc_block_residual( h, DCT_CHROMA_AC, 16+offset, h->dct.luma4x4[16+offset]+1 );
                x264_cavlc_block_residual( h, DCT_CHROMA_AC, 18+offset, h->dct.luma4x4[18+offset]+1 );
                x264_cavlc_block_residual( h, DCT_CHROMA_AC, 32+offset, h->dct.luma4x4[32+offset]+1 );
                x264_cavlc_block_residual( h, DCT_CHROMA_AC, 34+offset, h->dct.luma4x4[34+offset]+1 );
            }
            else
            {
                x264_cavlc_block_residual( h, DCT_CHROMA_AC, 16+i8, h->dct.luma4x4[16+i8]+1 );
                x264_cavlc_block_residual( h, DCT_CHROMA_AC, 32+i8, h->dct.luma4x4[32+i8]+1 );
            }
        }
        i8 += x264_pixel_size[i_pixel].h >> 3;
    }

    return h->out.bs.i_bits_encoded;
}

static int subpartition_size_cavlc( x264_t *h, int i4, int i_pixel )
{
    int plane_count = CHROMA444 ? 3 : 1;
    int b_8x4 = i_pixel == PIXEL_8x4;
    h->out.bs.i_bits_encoded = 0;
    cavlc_mvd( h, 0, i4, 1+b_8x4 );
    for( int p = 0; p < plane_count; p++ )
    {
        x264_cavlc_block_residual( h, DCT_LUMA_4x4, p*16+i4, h->dct.luma4x4[p*16+i4] );
        if( i_pixel != PIXEL_4x4 )
            x264_cavlc_block_residual( h, DCT_LUMA_4x4, p*16+i4+2-b_8x4, h->dct.luma4x4[p*16+i4+2-b_8x4] );
    }

    return h->out.bs.i_bits_encoded;
}

static int cavlc_intra4x4_pred_size( x264_t *h, int i4, int i_mode )
{
    if( x264_mb_predict_intra4x4_mode( h, i4 ) == x264_mb_pred_mode4x4_fix( i_mode ) )
        return 1;
    else
        return 4;
}

static int partition_i8x8_size_cavlc( x264_t *h, int i8, int i_mode )
{
    int plane_count = CHROMA444 ? 3 : 1;
    h->out.bs.i_bits_encoded = cavlc_intra4x4_pred_size( h, 4*i8, i_mode );
    //bs_write_ue( &h->out.bs, cbp_to_golomb[!CHROMA444][1][(h->mb.i_cbp_chroma << 4)|h->mb.i_cbp_luma] );
	uint8_t mask =
		(!!h->mb.cache.non_zero_count[x264_scan8[0 * 4]]) |
		((!!h->mb.cache.non_zero_count[x264_scan8[1 * 4]]) << 1) |
		((!!h->mb.cache.non_zero_count[x264_scan8[2 * 4]]) << 2) |
		((!!h->mb.cache.non_zero_count[x264_scan8[3 * 4]]) << 3);
	bs_write_ue(&h->out.bs, block_mask_to_golomb_table[(!!h->mb.cache.non_zero_count[x264_scan8[16 + 1 * 16]] << 5) | (!!h->mb.cache.non_zero_count[x264_scan8[16 + 0 * 16]] << 4) | mask]);
	if (h->mb.cache.non_zero_count[x264_scan8[i8 * 4]])
	{
		bs_write1(&h->out.bs, 1);//don't subdivide into 4x4
		h->mb.cache.non_zero_count[x264_scan8[i8 * 4]] = encode_dct(h, h->dct.luma8x8[i8], 64);
	}	
	//for( int p = 0; p < plane_count; p++ )
    //    cavlc_partition_luma_residual( h, i8, p );
    return h->out.bs.i_bits_encoded;
}

static int partition_i4x4_size_cavlc( x264_t *h, int i4, int i_mode )
{
    int plane_count = CHROMA444 ? 3 : 1;
    h->out.bs.i_bits_encoded = cavlc_intra4x4_pred_size( h, i4, i_mode );
	if (h->mb.cache.non_zero_count[x264_scan8[i4]])
		h->mb.cache.non_zero_count[x264_scan8[i4]] = encode_dct(h, h->dct.luma4x4[i4], 16);
	//for( int p = 0; p < plane_count; p++ )
    //    x264_cavlc_block_residual( h, DCT_LUMA_4x4, p*16+i4, h->dct.luma4x4[p*16+i4] );
    return h->out.bs.i_bits_encoded;
}

static int chroma_size_cavlc( x264_t *h )
{
	h->out.bs.i_bits_encoded = 3;//bs_size_ue( x264_mb_chroma_pred_mode_fix[h->mb.i_chroma_pred_mode] );
    /*if( h->mb.i_cbp_chroma )
    {
        x264_cavlc_block_residual( h, DCT_CHROMA_DC, CHROMA_DC+0, h->dct.chroma_dc[0] );
        x264_cavlc_block_residual( h, DCT_CHROMA_DC, CHROMA_DC+1, h->dct.chroma_dc[1] );

        if( h->mb.i_cbp_chroma == 2 )
        {
            int step = 8 << CHROMA_V_SHIFT;
            for( int i = 16; i < 3*16; i += step )
                for( int j = i; j < i+4; j++ )
                    x264_cavlc_block_residual( h, DCT_CHROMA_AC, j, h->dct.luma4x4[j]+1 );
        }
    }*/
	//todo: write plane params here when implemented and mode == 2
	for (int i = 0; i < 2; i++)
	{
		if (h->mb.cache.non_zero_count[x264_scan8[16 + i * 16]])
		{
			bs_write1(&h->out.bs, 1);//don't subdivide into 4x4
			h->mb.cache.non_zero_count[x264_scan8[16 + i * 16]] = encode_dct(h, h->dct.luma8x8[4 + 4 * i], 64);
		}
	}
    return h->out.bs.i_bits_encoded;
}
#endif
