#if !defined(CNF_DIFF_TEMPLATE_H__)
#define  CNF_DIFF_TEMPLATE_H__  1

// not-equal-or-0 templates
// results NOT forcedt to True

#include <stdint.h>
#include "cnf-templates.h"

#define  CNF_DIFF_MAX_ELEMS__  246


//----------------------------------------------------------------------------
static const uint8_t cnf_diff_template_ints[ 1670 ] = {  /* net 1626 +11*4 */
	2,1,4,3, 1,2,-3,0, -1,2,3,0, 1,-2,3,0, -1,-2,-3,0,  /*[20]*/
	          0,0,0,0,    /* separator */
	4,3,11,3, 1,3,-6,0, -1,3,6,0, 1,-3,6,0, -1,-3,-6,0, 2,4,-7,0, -2,4,7,0, 2,-4,7,0, -2,-4,-7,0, 6,7,-5,0, -6,5,0, -7,5,0,  /*[46]*/
	          0,0,0,0,    /* separator */
	6,4,16,4, 1,4,-8,0, -1,4,8,0, 1,-4,8,0, -1,-4,-8,0, 2,5,-9,0, -2,5,9,0, 2,-5,9,0, -2,-5,-9,0, 3,6,-10,0, -3,6,10,0, 3,-6,10,0, -3,-6,-10,0, 8,9,10,-7,0, -8,7,0, -9,7,0, -10,7,0,  /*[66]*/
	          0,0,0,0,    /* separator */
	8,5,21,5, 1,5,-10,0, -1,5,10,0, 1,-5,10,0, -1,-5,-10,0, 2,6,-11,0, -2,6,11,0, 2,-6,11,0, -2,-6,-11,0, 3,7,-12,0, -3,7,12,0, 3,-7,12,0, -3,-7,-12,0, 4,8,-13,0, -4,8,13,0, 4,-8,13,0, -4,-8,-13,0, 10,11,12,13,-9,0, -10,9,0, -11,9,0, -12,9,0, -13,9,0,  /*[86]*/
	          0,0,0,0,
	10,6,26,6, 1,6,-12,0, -1,6,12,0, 1,-6,12,0, -1,-6,-12,0, 2,7,-13,0, -2,7,13,0, 2,-7,13,0, -2,-7,-13,0, 3,8,-14,0, -3,8,14,0, 3,-8,14,0, -3,-8,-14,0, 4,9,-15,0, -4,9,15,0, 4,-9,15,0, -4,-9,-15,0, 5,10,-16,0, -5,10,16,0, 5,-10,16,0, -5,-10,-16,0, 12,13,14,15,16,-11,0, -12,11,0, -13,11,0, -14,11,0, -15,11,0, -16,11,0,  /*[106]*/
	          0,0,0,0,
	12,7,31,7, 1,7,-14,0, -1,7,14,0, 1,-7,14,0, -1,-7,-14,0, 2,8,-15,0, -2,8,15,0, 2,-8,15,0, -2,-8,-15,0, 3,9,-16,0, -3,9,16,0, 3,-9,16,0, -3,-9,-16,0, 4,10,-17,0, -4,10,17,0, 4,-10,17,0, -4,-10,-17,0, 5,11,-18,0, -5,11,18,0, 5,-11,18,0, -5,-11,-18,0, 6,12,-19,0, -6,12,19,0, 6,-12,19,0, -6,-12,-19,0, 14,15,16,17,18,19,-13,0, -14,13,0, -15,13,0, -16,13,0, -17,13,0, -18,13,0, -19,13,0,  /*[126]*/
	          0,0,0,0,
	14,8,36,8, 1,8,-16,0, -1,8,16,0, 1,-8,16,0, -1,-8,-16,0, 2,9,-17,0, -2,9,17,0, 2,-9,17,0, -2,-9,-17,0, 3,10,-18,0, -3,10,18,0, 3,-10,18,0, -3,-10,-18,0, 4,11,-19,0, -4,11,19,0, 4,-11,19,0, -4,-11,-19,0, 5,12,-20,0, -5,12,20,0, 5,-12,20,0, -5,-12,-20,0, 6,13,-21,0, -6,13,21,0, 6,-13,21,0, -6,-13,-21,0, 7,14,-22,0, -7,14,22,0, 7,-14,22,0, -7,-14,-22,0, 16,17,18,19,20,21,22,-15,0, -16,15,0, -17,15,0, -18,15,0, -19,15,0, -20,15,0, -21,15,0, -22,15,0,  /*[146]*/
	          0,0,0,0,
	16,9,41,9, 1,9,-18,0, -1,9,18,0, 1,-9,18,0, -1,-9,-18,0, 2,10,-19,0, -2,10,19,0, 2,-10,19,0, -2,-10,-19,0, 3,11,-20,0, -3,11,20,0, 3,-11,20,0, -3,-11,-20,0, 4,12,-21,0, -4,12,21,0, 4,-12,21,0, -4,-12,-21,0, 5,13,-22,0, -5,13,22,0, 5,-13,22,0, -5,-13,-22,0, 6,14,-23,0, -6,14,23,0, 6,-14,23,0, -6,-14,-23,0, 7,15,-24,0, -7,15,24,0, 7,-15,24,0, -7,-15,-24,0, 8,16,-25,0, -8,16,25,0, 8,-16,25,0, -8,-16,-25,0, 18,19,20,21,22,23,24,25,-17,0, -18,17,0, -19,17,0, -20,17,0, -21,17,0, -22,17,0, -23,17,0, -24,17,0, -25,17,0,  /*[166]*/
	          0,0,0,0,
	18,10,46,10, 1,10,-20,0, -1,10,20,0, 1,-10,20,0, -1,-10,-20,0, 2,11,-21,0, -2,11,21,0, 2,-11,21,0, -2,-11,-21,0, 3,12,-22,0, -3,12,22,0, 3,-12,22,0, -3,-12,-22,0, 4,13,-23,0, -4,13,23,0, 4,-13,23,0, -4,-13,-23,0, 5,14,-24,0, -5,14,24,0, 5,-14,24,0, -5,-14,-24,0, 6,15,-25,0, -6,15,25,0, 6,-15,25,0, -6,-15,-25,0, 7,16,-26,0, -7,16,26,0, 7,-16,26,0, -7,-16,-26,0, 8,17,-27,0, -8,17,27,0, 8,-17,27,0, -8,-17,-27,0, 9,18,-28,0, -9,18,28,0, 9,-18,28,0, -9,-18,-28,0, 20,21,22,23,24,25,26,27,28,-19,0, -20,19,0, -21,19,0, -22,19,0, -23,19,0, -24,19,0, -25,19,0, -26,19,0, -27,19,0, -28,19,0,  /*[186]*/
	          0,0,0,0,
	20,11,51,11, 1,11,-22,0, -1,11,22,0, 1,-11,22,0, -1,-11,-22,0, 2,12,-23,0, -2,12,23,0, 2,-12,23,0, -2,-12,-23,0, 3,13,-24,0, -3,13,24,0, 3,-13,24,0, -3,-13,-24,0, 4,14,-25,0, -4,14,25,0, 4,-14,25,0, -4,-14,-25,0, 5,15,-26,0, -5,15,26,0, 5,-15,26,0, -5,-15,-26,0, 6,16,-27,0, -6,16,27,0, 6,-16,27,0, -6,-16,-27,0, 7,17,-28,0, -7,17,28,0, 7,-17,28,0, -7,-17,-28,0, 8,18,-29,0, -8,18,29,0, 8,-18,29,0, -8,-18,-29,0, 9,19,-30,0, -9,19,30,0, 9,-19,30,0, -9,-19,-30,0, 10,20,-31,0, -10,20,31,0, 10,-20,31,0, -10,-20,-31,0, 22,23,24,25,26,27,28,29,30,31,-21,0, -22,21,0, -23,21,0, -24,21,0, -25,21,0, -26,21,0, -27,21,0, -28,21,0, -29,21,0, -30,21,0, -31,21,0,  /*[206]*/
	          0,0,0,0,
	22,12,56,12, 1,12,-24,0, -1,12,24,0, 1,-12,24,0, -1,-12,-24,0, 2,13,-25,0, -2,13,25,0, 2,-13,25,0, -2,-13,-25,0, 3,14,-26,0, -3,14,26,0, 3,-14,26,0, -3,-14,-26,0, 4,15,-27,0, -4,15,27,0, 4,-15,27,0, -4,-15,-27,0, 5,16,-28,0, -5,16,28,0, 5,-16,28,0, -5,-16,-28,0, 6,17,-29,0, -6,17,29,0, 6,-17,29,0, -6,-17,-29,0, 7,18,-30,0, -7,18,30,0, 7,-18,30,0, -7,-18,-30,0, 8,19,-31,0, -8,19,31,0, 8,-19,31,0, -8,-19,-31,0, 9,20,-32,0, -9,20,32,0, 9,-20,32,0, -9,-20,-32,0, 10,21,-33,0, -10,21,33,0, 10,-21,33,0, -10,-21,-33,0, 11,22,-34,0, -11,22,34,0, 11,-22,34,0, -11,-22,-34,0, 24,25,26,27,28,29,30,31,32,33,34,-23,0, -24,23,0, -25,23,0, -26,23,0, -27,23,0, -28,23,0, -29,23,0, -30,23,0, -31,23,0, -32,23,0, -33,23,0, -34,23,0,  /*[226]*/
	          0,0,0,0,
	24,13,61,13, 1,13,-26,0, -1,13,26,0, 1,-13,26,0, -1,-13,-26,0, 2,14,-27,0, -2,14,27,0, 2,-14,27,0, -2,-14,-27,0, 3,15,-28,0, -3,15,28,0, 3,-15,28,0, -3,-15,-28,0, 4,16,-29,0, -4,16,29,0, 4,-16,29,0, -4,-16,-29,0, 5,17,-30,0, -5,17,30,0, 5,-17,30,0, -5,-17,-30,0, 6,18,-31,0, -6,18,31,0, 6,-18,31,0, -6,-18,-31,0, 7,19,-32,0, -7,19,32,0, 7,-19,32,0, -7,-19,-32,0, 8,20,-33,0, -8,20,33,0, 8,-20,33,0, -8,-20,-33,0, 9,21,-34,0, -9,21,34,0, 9,-21,34,0, -9,-21,-34,0, 10,22,-35,0, -10,22,35,0, 10,-22,35,0, -10,-22,-35,0, 11,23,-36,0, -11,23,36,0, 11,-23,36,0, -11,-23,-36,0, 12,24,-37,0, -12,24,37,0, 12,-24,37,0, -12,-24,-37,0, 26,27,28,29,30,31,32,33,34,35,36,37,-25,0, -26,25,0, -27,25,0, -28,25,0, -29,25,0, -30,25,0, -31,25,0, -32,25,0, -33,25,0, -34,25,0, -35,25,0, -36,25,0, -37,25,0,  /*[246]*/
} ;


    /* index into cnf_diff_template_ints */
static const struct TemplIndex cnf_diff_template_ints_idx[ 12 ] = {
	{    0,  20 },
	{   24,  46 },
	{   74,  66 },
	{  144,  86 },
	{  234, 106 },
	{  344, 126 },
	{  474, 146 },
	{  624, 166 },
	{  794, 186 },
	{  984, 206 },
	{ 1194, 226 },
	{ 1424, 246 },
} ;

#endif  /* !def(CNF_DIFF_TEMPLATE_H__) */
