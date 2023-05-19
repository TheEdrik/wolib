#include <stdint.h>

// P=1-of-3 x Q=1-of-4
// VARS(P)[3]=['XY12C86', 'XY12C87', 'XY12C88']
// VARS(Q)[4]=['XY12R89', 'XY12R90', 'XY12R91', 'XY12R92']
// P=1-of-2 x Q=1-of-2
// VARS(P)[2]=['XY4C95', 'XY4C96']
// VARS(Q)[2]=['XY4R97', 'XY4R98']
// VAR.P=N1xXOR99 [4]  [' XY4C95  XY4C96 -N1xXOR99', '-XY4C95  XY4C96  N1xXOR99', ' XY4C95 -XY4C96  N1xXOR99', '-XY4C95 -XY4C96 -N1xXOR99']
// VAR.Q=N1xXOR100 [4]  [' XY4R97  XY4R98 -N1xXOR100', '-XY4R97  XY4R98  N1xXOR100', ' XY4R97 -XY4R98  N1xXOR100', '-XY4R97 -XY4R98 -N1xXOR100']
// ADDED.VARS=+7
// ADDED.VARS=[N1x94, XY4C95, XY4C96, XY4R97, XY4R98, N1xXOR99, N1xXOR100]
// VAR.P=[] [7]  ['-XY12C86 -XY12C87', '-XY12C86 -XY12C88', '-XY12C87 -XY12C88', 'XY12C86 XY12C87 XY12C88 -THREE2ONEx93', '-XY12C86 THREE2ONEx93', '-XY12C87 THREE2ONEx93', '-XY12C88 THREE2ONEx93']
// VAR.Q=N1x94 [17]  [' XY4C95  XY4C96 -N1xXOR99', '-XY4C95  XY4C96  N1xXOR99', ' XY4C95 -XY4C96  N1xXOR99', '-XY4C95 -XY4C96 -N1xXOR99', ' XY4R97  XY4R98 -N1xXOR100', '-XY4R97  XY4R98  N1xXOR100', ' XY4R97 -XY4R98  N1xXOR100', '-XY4R97 -XY4R98 -N1xXOR100', '-XY12R89 XY4C95', '-XY12R89 XY4R97', '-XY12R90 XY4C96', '-XY12R90 XY4R97', '-XY12R91 XY4C95', '-XY12R91 XY4R98', '-XY12R92 XY4C96', '-XY12R92 XY4R98', 'N1x94']
// ADDED.VARS=+16
// ADDED.VARS=[N1x85, XY12C86, XY12C87, XY12C88, XY12R89, XY12R90, XY12R91, XY12R92, THREE2ONEx93, N1x94, XY4C95, XY4C96, XY4R97, XY4R98, N1xXOR99, N1xXOR100]
// 1-of-N[12] r=N1x85 cls[49]=['-XY12C86 -XY12C87', '-XY12C86 -XY12C88', '-XY12C87 -XY12C88', 'XY12C86 XY12C87 XY12C88 -THREE2ONEx93', '-XY12C86 THREE2ONEx93', '-XY12C87 THREE2ONEx93', '-XY12C88 THREE2ONEx93', ' XY4C95  XY4C96 -N1xXOR99', '-XY4C95  XY4C96  N1xXOR99', ' XY4C95 -XY4C96  N1xXOR99', '-XY4C95 -XY4C96 -N1xXOR99', ' XY4R97  XY4R98 -N1xXOR100', '-XY4R97  XY4R98  N1xXOR100', ' XY4R97 -XY4R98  N1xXOR100', '-XY4R97 -XY4R98 -N1xXOR100', '-XY12R89 XY4C95', '-XY12R89 XY4R97', '-XY12R90 XY4C96', '-XY12R90 XY4R97', '-XY12R91 XY4C95', '-XY12R91 XY4R98', '-XY12R92 XY4C96', '-XY12R92 XY4R98', 'N1x94', '-v000 XY12C86', '-v000 XY12R89', '-v001 XY12C87', '-v001 XY12R89', '-v002 XY12C88', '-v002 XY12R89', '-v003 XY12C86', '-v003 XY12R90', '-v004 XY12C87', '-v004 XY12R90', '-v005 XY12C88', '-v005 XY12R90', '-v006 XY12C86', '-v006 XY12R91', '-v007 XY12C87', '-v007 XY12R91', '-v008 XY12C88', '-v008 XY12R91', '-v009 XY12C86', '-v009 XY12R92', '-v010 XY12C87', '-v010 XY12R92', '-v011 XY12C88', '-v011 XY12R92', 'N1x85'] [] 1-of-12 <-> 3*4
// ['-', '-'] ['XY12C86', 'XY12C87'] [13, 14]
// ['-', '-'] ['XY12C86', 'XY12C88'] [13, 15]
// ['-', '-'] ['XY12C87', 'XY12C88'] [14, 15]
// ['', '', '', '-'] ['XY12C86', 'XY12C87', 'XY12C88', 'THREE2ONEx93'] [13, 14, 15, 16]
// ['-', ''] ['XY12C86', 'THREE2ONEx93'] [13, 16]
// ['-', ''] ['XY12C87', 'THREE2ONEx93'] [14, 16]
// ['-', ''] ['XY12C88', 'THREE2ONEx93'] [15, 16]
// ['', '', '-'] ['XY4C95', 'XY4C96', 'N1xXOR99'] [17, 18, 19]
// ['-', '', ''] ['XY4C95', 'XY4C96', 'N1xXOR99'] [17, 18, 19]
// ['', '-', ''] ['XY4C95', 'XY4C96', 'N1xXOR99'] [17, 18, 19]
// ['-', '-', '-'] ['XY4C95', 'XY4C96', 'N1xXOR99'] [17, 18, 19]
// ['', '', '-'] ['XY4R97', 'XY4R98', 'N1xXOR100'] [20, 21, 22]
// ['-', '', ''] ['XY4R97', 'XY4R98', 'N1xXOR100'] [20, 21, 22]
// ['', '-', ''] ['XY4R97', 'XY4R98', 'N1xXOR100'] [20, 21, 22]
// ['-', '-', '-'] ['XY4R97', 'XY4R98', 'N1xXOR100'] [20, 21, 22]
// ['-', ''] ['XY12R89', 'XY4C95'] [23, 17]
// ['-', ''] ['XY12R89', 'XY4R97'] [23, 20]
// ['-', ''] ['XY12R90', 'XY4C96'] [24, 18]
// ['-', ''] ['XY12R90', 'XY4R97'] [24, 20]
// ['-', ''] ['XY12R91', 'XY4C95'] [25, 17]
// ['-', ''] ['XY12R91', 'XY4R98'] [25, 21]
// ['-', ''] ['XY12R92', 'XY4C96'] [26, 18]
// ['-', ''] ['XY12R92', 'XY4R98'] [26, 21]
// [''] ['N1x94'] [27]
// ['-', ''] ['v000', 'XY12C86'] [1, 13]
// ['-', ''] ['v000', 'XY12R89'] [1, 23]
// ['-', ''] ['v001', 'XY12C87'] [2, 14]
// ['-', ''] ['v001', 'XY12R89'] [2, 23]
// ['-', ''] ['v002', 'XY12C88'] [3, 15]
// ['-', ''] ['v002', 'XY12R89'] [3, 23]
// ['-', ''] ['v003', 'XY12C86'] [4, 13]
// ['-', ''] ['v003', 'XY12R90'] [4, 24]
// ['-', ''] ['v004', 'XY12C87'] [5, 14]
// ['-', ''] ['v004', 'XY12R90'] [5, 24]
// ['-', ''] ['v005', 'XY12C88'] [6, 15]
// ['-', ''] ['v005', 'XY12R90'] [6, 24]
// ['-', ''] ['v006', 'XY12C86'] [7, 13]
// ['-', ''] ['v006', 'XY12R91'] [7, 25]
// ['-', ''] ['v007', 'XY12C87'] [8, 14]
// ['-', ''] ['v007', 'XY12R91'] [8, 25]
// ['-', ''] ['v008', 'XY12C88'] [9, 15]
// ['-', ''] ['v008', 'XY12R91'] [9, 25]
// ['-', ''] ['v009', 'XY12C86'] [10, 13]
// ['-', ''] ['v009', 'XY12R92'] [10, 26]
// ['-', ''] ['v010', 'XY12C87'] [11, 14]
// ['-', ''] ['v010', 'XY12R92'] [11, 26]
// ['-', ''] ['v011', 'XY12C88'] [12, 15]
// ['-', ''] ['v011', 'XY12R92'] [12, 26]
// [''] ['N1x85'] [28]
#if !defined(CNF_TEMPLATEHDR_ELEMS)
/* first elements storing input/additional-var count (2)
 * and max-nr-of-variables per clause (+1)
 */
#define CNF_TEMPLATEHDR_ELEMS ((unsigned int) 3)
#endif
/**/
// CLAUSES[TYPE=uint8_t][12+16 variables]:
static const uint8_t __NAME__1_OF_NEQ12__[] = {
0x0c,0x10,0x04,
//
0xcd,0xce,0x00,
0xcd,0xcf,0x00,
0xce,0xcf,0x00,
0x4d,0x4e,0x4f,0xd0,0x00,
0xcd,0x50,0x00,
0xce,0x50,0x00,
0xcf,0x50,0x00,
0x51,0x52,0xd3,0x00,
0xd1,0x52,0x53,0x00,
0x51,0xd2,0x53,0x00,
0xd1,0xd2,0xd3,0x00,
0x54,0x55,0xd6,0x00,
0xd4,0x55,0x56,0x00,
0x54,0xd5,0x56,0x00,
0xd4,0xd5,0xd6,0x00,
0xd7,0x51,0x00,
0xd7,0x54,0x00,
0xd8,0x52,0x00,
0xd8,0x54,0x00,
0xd9,0x51,0x00,
0xd9,0x55,0x00,
0xda,0x52,0x00,
0xda,0x55,0x00,
0x5b,0x00,
0x81,0x4d,0x00,
0x81,0x57,0x00,
0x82,0x4e,0x00,
0x82,0x57,0x00,
0x83,0x4f,0x00,
0x83,0x57,0x00,
0x84,0x4d,0x00,
0x84,0x58,0x00,
0x85,0x4e,0x00,
0x85,0x58,0x00,
0x86,0x4f,0x00,
0x86,0x58,0x00,
0x87,0x4d,0x00,
0x87,0x59,0x00,
0x88,0x4e,0x00,
0x88,0x59,0x00,
0x89,0x4f,0x00,
0x89,0x59,0x00,
0x8a,0x4d,0x00,
0x8a,0x5a,0x00,
0x8b,0x4e,0x00,
0x8b,0x5a,0x00,
0x8c,0x4f,0x00,
0x8c,0x5a,0x00,
0x5c,0x00,
} ;
// /CLAUSES

