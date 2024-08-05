#if !defined(CNF_AND_TEMPLATE_H__)
#define  CNF_AND_TEMPLATE_H__  1

/* AND templates for 1..63 variables */

#include <stdint.h>
#include "cnf-templates.h"

#define  CNF_AND_MAX_ELEMS__  262


//----------------------------------------------------------------------------
static const int cnf_and_template_ints[ 8942 ] = {         /* net 8694 +62*4 */
	2,1,3,3, -1,-2,3,0, 1,-3,0, 2,-3,0,  /*[14]*/ /*[0.]*/
	          0,0,0,0,    /* separator */
	3,1,4,4, -1,-2,-3,4,0, 1,-4,0, 2,-4,0, 3,-4,0,  /*[18]*/ /*[1.]*/
	          0,0,0,0,    /* separator */
	4,1,5,5, -1,-2,-3,-4,5,0, 1,-5,0, 2,-5,0, 3,-5,0, 4,-5,0,  /*[22]*/ /*[2.]*/
	          0,0,0,0,    /* separator */
	5,1,6,6, -1,-2,-3,-4,-5,6,0, 1,-6,0, 2,-6,0, 3,-6,0, 4,-6,0, 5,-6,0,  /*[26]*/ /*[3.]*/
	          0,0,0,0,
	6,1,7,7, -1,-2,-3,-4,-5,-6,7,0, 1,-7,0, 2,-7,0, 3,-7,0, 4,-7,0, 5,-7,0, 6,-7,0,  /*[30]*/ /*[4.]*/
	          0,0,0,0,
	7,1,8,8, -1,-2,-3,-4,-5,-6,-7,8,0, 1,-8,0, 2,-8,0, 3,-8,0, 4,-8,0, 5,-8,0, 6,-8,0, 7,-8,0,  /*[34]*/ /*[5.]*/
	          0,0,0,0,
	8,1,9,9, -1,-2,-3,-4,-5,-6,-7,-8,9,0, 1,-9,0, 2,-9,0, 3,-9,0, 4,-9,0, 5,-9,0, 6,-9,0, 7,-9,0, 8,-9,0,  /*[38]*/ /*[6.]*/
	          0,0,0,0,
	9,1,10,10, -1,-2,-3,-4,-5,-6,-7,-8,-9,10,0, 1,-10,0, 2,-10,0, 3,-10,0, 4,-10,0, 5,-10,0, 6,-10,0, 7,-10,0, 8,-10,0, 9,-10,0,  /*[42]*/ /*[7.]*/
	          0,0,0,0,
	10,1,11,11, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,11,0, 1,-11,0, 2,-11,0, 3,-11,0, 4,-11,0, 5,-11,0, 6,-11,0, 7,-11,0, 8,-11,0, 9,-11,0, 10,-11,0,  /*[46]*/ /*[8.]*/
	          0,0,0,0,
	11,1,12,12, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,12,0, 1,-12,0, 2,-12,0, 3,-12,0, 4,-12,0, 5,-12,0, 6,-12,0, 7,-12,0, 8,-12,0, 9,-12,0, 10,-12,0, 11,-12,0,  /*[50]*/ /*[9.]*/
	          0,0,0,0,
	12,1,13,13, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,13,0, 1,-13,0, 2,-13,0, 3,-13,0, 4,-13,0, 5,-13,0, 6,-13,0, 7,-13,0, 8,-13,0, 9,-13,0, 10,-13,0, 11,-13,0, 12,-13,0,  /*[54]*/ /*[10.]*/
	          0,0,0,0,
	13,1,14,14, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,14,0, 1,-14,0, 2,-14,0, 3,-14,0, 4,-14,0, 5,-14,0, 6,-14,0, 7,-14,0, 8,-14,0, 9,-14,0, 10,-14,0, 11,-14,0, 12,-14,0, 13,-14,0,  /*[58]*/ /*[11.]*/
	          0,0,0,0,
	14,1,15,15, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,15,0, 1,-15,0, 2,-15,0, 3,-15,0, 4,-15,0, 5,-15,0, 6,-15,0, 7,-15,0, 8,-15,0, 9,-15,0, 10,-15,0, 11,-15,0, 12,-15,0, 13,-15,0, 14,-15,0,  /*[62]*/ /*[12.]*/
	          0,0,0,0,
	15,1,16,16, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,16,0, 1,-16,0, 2,-16,0, 3,-16,0, 4,-16,0, 5,-16,0, 6,-16,0, 7,-16,0, 8,-16,0, 9,-16,0, 10,-16,0, 11,-16,0, 12,-16,0, 13,-16,0, 14,-16,0, 15,-16,0,  /*[66]*/ /*[13.]*/
	          0,0,0,0,
	16,1,17,17, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,17,0, 1,-17,0, 2,-17,0, 3,-17,0, 4,-17,0, 5,-17,0, 6,-17,0, 7,-17,0, 8,-17,0, 9,-17,0, 10,-17,0, 11,-17,0, 12,-17,0, 13,-17,0, 14,-17,0, 15,-17,0, 16,-17,0,  /*[70]*/ /*[14.]*/
	          0,0,0,0,
	17,1,18,18, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,18,0, 1,-18,0, 2,-18,0, 3,-18,0, 4,-18,0, 5,-18,0, 6,-18,0, 7,-18,0, 8,-18,0, 9,-18,0, 10,-18,0, 11,-18,0, 12,-18,0, 13,-18,0, 14,-18,0, 15,-18,0, 16,-18,0, 17,-18,0,  /*[74]*/ /*[15.]*/
	          0,0,0,0,
	18,1,19,19, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,19,0, 1,-19,0, 2,-19,0, 3,-19,0, 4,-19,0, 5,-19,0, 6,-19,0, 7,-19,0, 8,-19,0, 9,-19,0, 10,-19,0, 11,-19,0, 12,-19,0, 13,-19,0, 14,-19,0, 15,-19,0, 16,-19,0, 17,-19,0, 18,-19,0,  /*[78]*/ /*[16.]*/
	          0,0,0,0,
	19,1,20,20, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,20,0, 1,-20,0, 2,-20,0, 3,-20,0, 4,-20,0, 5,-20,0, 6,-20,0, 7,-20,0, 8,-20,0, 9,-20,0, 10,-20,0, 11,-20,0, 12,-20,0, 13,-20,0, 14,-20,0, 15,-20,0, 16,-20,0, 17,-20,0, 18,-20,0, 19,-20,0,  /*[82]*/ /*[17.]*/
	          0,0,0,0,
	20,1,21,21, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,21,0, 1,-21,0, 2,-21,0, 3,-21,0, 4,-21,0, 5,-21,0, 6,-21,0, 7,-21,0, 8,-21,0, 9,-21,0, 10,-21,0, 11,-21,0, 12,-21,0, 13,-21,0, 14,-21,0, 15,-21,0, 16,-21,0, 17,-21,0, 18,-21,0, 19,-21,0, 20,-21,0,  /*[86]*/ /*[18.]*/
	          0,0,0,0,
	21,1,22,22, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,22,0, 1,-22,0, 2,-22,0, 3,-22,0, 4,-22,0, 5,-22,0, 6,-22,0, 7,-22,0, 8,-22,0, 9,-22,0, 10,-22,0, 11,-22,0, 12,-22,0, 13,-22,0, 14,-22,0, 15,-22,0, 16,-22,0, 17,-22,0, 18,-22,0, 19,-22,0, 20,-22,0, 21,-22,0,  /*[90]*/ /*[19.]*/
	          0,0,0,0,
	22,1,23,23, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,23,0, 1,-23,0, 2,-23,0, 3,-23,0, 4,-23,0, 5,-23,0, 6,-23,0, 7,-23,0, 8,-23,0, 9,-23,0, 10,-23,0, 11,-23,0, 12,-23,0, 13,-23,0, 14,-23,0, 15,-23,0, 16,-23,0, 17,-23,0, 18,-23,0, 19,-23,0, 20,-23,0, 21,-23,0, 22,-23,0,  /*[94]*/ /*[20.]*/
	          0,0,0,0,
	23,1,24,24, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,24,0, 1,-24,0, 2,-24,0, 3,-24,0, 4,-24,0, 5,-24,0, 6,-24,0, 7,-24,0, 8,-24,0, 9,-24,0, 10,-24,0, 11,-24,0, 12,-24,0, 13,-24,0, 14,-24,0, 15,-24,0, 16,-24,0, 17,-24,0, 18,-24,0, 19,-24,0, 20,-24,0, 21,-24,0, 22,-24,0, 23,-24,0,  /*[98]*/ /*[21.]*/
	          0,0,0,0,
	24,1,25,25, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,25,0, 1,-25,0, 2,-25,0, 3,-25,0, 4,-25,0, 5,-25,0, 6,-25,0, 7,-25,0, 8,-25,0, 9,-25,0, 10,-25,0, 11,-25,0, 12,-25,0, 13,-25,0, 14,-25,0, 15,-25,0, 16,-25,0, 17,-25,0, 18,-25,0, 19,-25,0, 20,-25,0, 21,-25,0, 22,-25,0, 23,-25,0, 24,-25,0,  /*[102]*/ /*[22.]*/
	          0,0,0,0,
	25,1,26,26, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,26,0, 1,-26,0, 2,-26,0, 3,-26,0, 4,-26,0, 5,-26,0, 6,-26,0, 7,-26,0, 8,-26,0, 9,-26,0, 10,-26,0, 11,-26,0, 12,-26,0, 13,-26,0, 14,-26,0, 15,-26,0, 16,-26,0, 17,-26,0, 18,-26,0, 19,-26,0, 20,-26,0, 21,-26,0, 22,-26,0, 23,-26,0, 24,-26,0, 25,-26,0,  /*[106]*/ /*[23.]*/
	          0,0,0,0,
	26,1,27,27, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,27,0, 1,-27,0, 2,-27,0, 3,-27,0, 4,-27,0, 5,-27,0, 6,-27,0, 7,-27,0, 8,-27,0, 9,-27,0, 10,-27,0, 11,-27,0, 12,-27,0, 13,-27,0, 14,-27,0, 15,-27,0, 16,-27,0, 17,-27,0, 18,-27,0, 19,-27,0, 20,-27,0, 21,-27,0, 22,-27,0, 23,-27,0, 24,-27,0, 25,-27,0, 26,-27,0,  /*[110]*/ /*[24.]*/
	          0,0,0,0,
	27,1,28,28, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,28,0, 1,-28,0, 2,-28,0, 3,-28,0, 4,-28,0, 5,-28,0, 6,-28,0, 7,-28,0, 8,-28,0, 9,-28,0, 10,-28,0, 11,-28,0, 12,-28,0, 13,-28,0, 14,-28,0, 15,-28,0, 16,-28,0, 17,-28,0, 18,-28,0, 19,-28,0, 20,-28,0, 21,-28,0, 22,-28,0, 23,-28,0, 24,-28,0, 25,-28,0, 26,-28,0, 27,-28,0,  /*[114]*/ /*[25.]*/
	          0,0,0,0,
	28,1,29,29, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,29,0, 1,-29,0, 2,-29,0, 3,-29,0, 4,-29,0, 5,-29,0, 6,-29,0, 7,-29,0, 8,-29,0, 9,-29,0, 10,-29,0, 11,-29,0, 12,-29,0, 13,-29,0, 14,-29,0, 15,-29,0, 16,-29,0, 17,-29,0, 18,-29,0, 19,-29,0, 20,-29,0, 21,-29,0, 22,-29,0, 23,-29,0, 24,-29,0, 25,-29,0, 26,-29,0, 27,-29,0, 28,-29,0,  /*[118]*/ /*[26.]*/
	          0,0,0,0,
	29,1,30,30, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,30,0, 1,-30,0, 2,-30,0, 3,-30,0, 4,-30,0, 5,-30,0, 6,-30,0, 7,-30,0, 8,-30,0, 9,-30,0, 10,-30,0, 11,-30,0, 12,-30,0, 13,-30,0, 14,-30,0, 15,-30,0, 16,-30,0, 17,-30,0, 18,-30,0, 19,-30,0, 20,-30,0, 21,-30,0, 22,-30,0, 23,-30,0, 24,-30,0, 25,-30,0, 26,-30,0, 27,-30,0, 28,-30,0, 29,-30,0,  /*[122]*/ /*[27.]*/
	          0,0,0,0,
	30,1,31,31, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,31,0, 1,-31,0, 2,-31,0, 3,-31,0, 4,-31,0, 5,-31,0, 6,-31,0, 7,-31,0, 8,-31,0, 9,-31,0, 10,-31,0, 11,-31,0, 12,-31,0, 13,-31,0, 14,-31,0, 15,-31,0, 16,-31,0, 17,-31,0, 18,-31,0, 19,-31,0, 20,-31,0, 21,-31,0, 22,-31,0, 23,-31,0, 24,-31,0, 25,-31,0, 26,-31,0, 27,-31,0, 28,-31,0, 29,-31,0, 30,-31,0,  /*[126]*/ /*[28.]*/
	          0,0,0,0,
	31,1,32,32, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,32,0, 1,-32,0, 2,-32,0, 3,-32,0, 4,-32,0, 5,-32,0, 6,-32,0, 7,-32,0, 8,-32,0, 9,-32,0, 10,-32,0, 11,-32,0, 12,-32,0, 13,-32,0, 14,-32,0, 15,-32,0, 16,-32,0, 17,-32,0, 18,-32,0, 19,-32,0, 20,-32,0, 21,-32,0, 22,-32,0, 23,-32,0, 24,-32,0, 25,-32,0, 26,-32,0, 27,-32,0, 28,-32,0, 29,-32,0, 30,-32,0, 31,-32,0,  /*[130]*/ /*[29.]*/
	          0,0,0,0,
	32,1,33,33, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,33,0, 1,-33,0, 2,-33,0, 3,-33,0, 4,-33,0, 5,-33,0, 6,-33,0, 7,-33,0, 8,-33,0, 9,-33,0, 10,-33,0, 11,-33,0, 12,-33,0, 13,-33,0, 14,-33,0, 15,-33,0, 16,-33,0, 17,-33,0, 18,-33,0, 19,-33,0, 20,-33,0, 21,-33,0, 22,-33,0, 23,-33,0, 24,-33,0, 25,-33,0, 26,-33,0, 27,-33,0, 28,-33,0, 29,-33,0, 30,-33,0, 31,-33,0, 32,-33,0,  /*[134]*/ /*[30.]*/
	          0,0,0,0,
	33,1,34,34, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,34,0, 1,-34,0, 2,-34,0, 3,-34,0, 4,-34,0, 5,-34,0, 6,-34,0, 7,-34,0, 8,-34,0, 9,-34,0, 10,-34,0, 11,-34,0, 12,-34,0, 13,-34,0, 14,-34,0, 15,-34,0, 16,-34,0, 17,-34,0, 18,-34,0, 19,-34,0, 20,-34,0, 21,-34,0, 22,-34,0, 23,-34,0, 24,-34,0, 25,-34,0, 26,-34,0, 27,-34,0, 28,-34,0, 29,-34,0, 30,-34,0, 31,-34,0, 32,-34,0, 33,-34,0,  /*[138]*/ /*[31.]*/
	          0,0,0,0,
	34,1,35,35, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,35,0, 1,-35,0, 2,-35,0, 3,-35,0, 4,-35,0, 5,-35,0, 6,-35,0, 7,-35,0, 8,-35,0, 9,-35,0, 10,-35,0, 11,-35,0, 12,-35,0, 13,-35,0, 14,-35,0, 15,-35,0, 16,-35,0, 17,-35,0, 18,-35,0, 19,-35,0, 20,-35,0, 21,-35,0, 22,-35,0, 23,-35,0, 24,-35,0, 25,-35,0, 26,-35,0, 27,-35,0, 28,-35,0, 29,-35,0, 30,-35,0, 31,-35,0, 32,-35,0, 33,-35,0, 34,-35,0,  /*[142]*/ /*[32.]*/
	          0,0,0,0,
	35,1,36,36, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,36,0, 1,-36,0, 2,-36,0, 3,-36,0, 4,-36,0, 5,-36,0, 6,-36,0, 7,-36,0, 8,-36,0, 9,-36,0, 10,-36,0, 11,-36,0, 12,-36,0, 13,-36,0, 14,-36,0, 15,-36,0, 16,-36,0, 17,-36,0, 18,-36,0, 19,-36,0, 20,-36,0, 21,-36,0, 22,-36,0, 23,-36,0, 24,-36,0, 25,-36,0, 26,-36,0, 27,-36,0, 28,-36,0, 29,-36,0, 30,-36,0, 31,-36,0, 32,-36,0, 33,-36,0, 34,-36,0, 35,-36,0,  /*[146]*/ /*[33.]*/
	          0,0,0,0,
	36,1,37,37, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,37,0, 1,-37,0, 2,-37,0, 3,-37,0, 4,-37,0, 5,-37,0, 6,-37,0, 7,-37,0, 8,-37,0, 9,-37,0, 10,-37,0, 11,-37,0, 12,-37,0, 13,-37,0, 14,-37,0, 15,-37,0, 16,-37,0, 17,-37,0, 18,-37,0, 19,-37,0, 20,-37,0, 21,-37,0, 22,-37,0, 23,-37,0, 24,-37,0, 25,-37,0, 26,-37,0, 27,-37,0, 28,-37,0, 29,-37,0, 30,-37,0, 31,-37,0, 32,-37,0, 33,-37,0, 34,-37,0, 35,-37,0, 36,-37,0,  /*[150]*/ /*[34.]*/
	          0,0,0,0,
	37,1,38,38, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,38,0, 1,-38,0, 2,-38,0, 3,-38,0, 4,-38,0, 5,-38,0, 6,-38,0, 7,-38,0, 8,-38,0, 9,-38,0, 10,-38,0, 11,-38,0, 12,-38,0, 13,-38,0, 14,-38,0, 15,-38,0, 16,-38,0, 17,-38,0, 18,-38,0, 19,-38,0, 20,-38,0, 21,-38,0, 22,-38,0, 23,-38,0, 24,-38,0, 25,-38,0, 26,-38,0, 27,-38,0, 28,-38,0, 29,-38,0, 30,-38,0, 31,-38,0, 32,-38,0, 33,-38,0, 34,-38,0, 35,-38,0, 36,-38,0, 37,-38,0,  /*[154]*/ /*[35.]*/
	          0,0,0,0,
	38,1,39,39, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,39,0, 1,-39,0, 2,-39,0, 3,-39,0, 4,-39,0, 5,-39,0, 6,-39,0, 7,-39,0, 8,-39,0, 9,-39,0, 10,-39,0, 11,-39,0, 12,-39,0, 13,-39,0, 14,-39,0, 15,-39,0, 16,-39,0, 17,-39,0, 18,-39,0, 19,-39,0, 20,-39,0, 21,-39,0, 22,-39,0, 23,-39,0, 24,-39,0, 25,-39,0, 26,-39,0, 27,-39,0, 28,-39,0, 29,-39,0, 30,-39,0, 31,-39,0, 32,-39,0, 33,-39,0, 34,-39,0, 35,-39,0, 36,-39,0, 37,-39,0, 38,-39,0,  /*[158]*/ /*[36.]*/
	          0,0,0,0,
	39,1,40,40, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,40,0, 1,-40,0, 2,-40,0, 3,-40,0, 4,-40,0, 5,-40,0, 6,-40,0, 7,-40,0, 8,-40,0, 9,-40,0, 10,-40,0, 11,-40,0, 12,-40,0, 13,-40,0, 14,-40,0, 15,-40,0, 16,-40,0, 17,-40,0, 18,-40,0, 19,-40,0, 20,-40,0, 21,-40,0, 22,-40,0, 23,-40,0, 24,-40,0, 25,-40,0, 26,-40,0, 27,-40,0, 28,-40,0, 29,-40,0, 30,-40,0, 31,-40,0, 32,-40,0, 33,-40,0, 34,-40,0, 35,-40,0, 36,-40,0, 37,-40,0, 38,-40,0, 39,-40,0,  /*[162]*/ /*[37.]*/
	          0,0,0,0,
	40,1,41,41, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,41,0, 1,-41,0, 2,-41,0, 3,-41,0, 4,-41,0, 5,-41,0, 6,-41,0, 7,-41,0, 8,-41,0, 9,-41,0, 10,-41,0, 11,-41,0, 12,-41,0, 13,-41,0, 14,-41,0, 15,-41,0, 16,-41,0, 17,-41,0, 18,-41,0, 19,-41,0, 20,-41,0, 21,-41,0, 22,-41,0, 23,-41,0, 24,-41,0, 25,-41,0, 26,-41,0, 27,-41,0, 28,-41,0, 29,-41,0, 30,-41,0, 31,-41,0, 32,-41,0, 33,-41,0, 34,-41,0, 35,-41,0, 36,-41,0, 37,-41,0, 38,-41,0, 39,-41,0, 40,-41,0,  /*[166]*/ /*[38.]*/
	          0,0,0,0,
	41,1,42,42, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,42,0, 1,-42,0, 2,-42,0, 3,-42,0, 4,-42,0, 5,-42,0, 6,-42,0, 7,-42,0, 8,-42,0, 9,-42,0, 10,-42,0, 11,-42,0, 12,-42,0, 13,-42,0, 14,-42,0, 15,-42,0, 16,-42,0, 17,-42,0, 18,-42,0, 19,-42,0, 20,-42,0, 21,-42,0, 22,-42,0, 23,-42,0, 24,-42,0, 25,-42,0, 26,-42,0, 27,-42,0, 28,-42,0, 29,-42,0, 30,-42,0, 31,-42,0, 32,-42,0, 33,-42,0, 34,-42,0, 35,-42,0, 36,-42,0, 37,-42,0, 38,-42,0, 39,-42,0, 40,-42,0, 41,-42,0,  /*[170]*/ /*[39.]*/
	          0,0,0,0,
	42,1,43,43, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,43,0, 1,-43,0, 2,-43,0, 3,-43,0, 4,-43,0, 5,-43,0, 6,-43,0, 7,-43,0, 8,-43,0, 9,-43,0, 10,-43,0, 11,-43,0, 12,-43,0, 13,-43,0, 14,-43,0, 15,-43,0, 16,-43,0, 17,-43,0, 18,-43,0, 19,-43,0, 20,-43,0, 21,-43,0, 22,-43,0, 23,-43,0, 24,-43,0, 25,-43,0, 26,-43,0, 27,-43,0, 28,-43,0, 29,-43,0, 30,-43,0, 31,-43,0, 32,-43,0, 33,-43,0, 34,-43,0, 35,-43,0, 36,-43,0, 37,-43,0, 38,-43,0, 39,-43,0, 40,-43,0, 41,-43,0, 42,-43,0,  /*[174]*/ /*[40.]*/
	          0,0,0,0,
	43,1,44,44, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,44,0, 1,-44,0, 2,-44,0, 3,-44,0, 4,-44,0, 5,-44,0, 6,-44,0, 7,-44,0, 8,-44,0, 9,-44,0, 10,-44,0, 11,-44,0, 12,-44,0, 13,-44,0, 14,-44,0, 15,-44,0, 16,-44,0, 17,-44,0, 18,-44,0, 19,-44,0, 20,-44,0, 21,-44,0, 22,-44,0, 23,-44,0, 24,-44,0, 25,-44,0, 26,-44,0, 27,-44,0, 28,-44,0, 29,-44,0, 30,-44,0, 31,-44,0, 32,-44,0, 33,-44,0, 34,-44,0, 35,-44,0, 36,-44,0, 37,-44,0, 38,-44,0, 39,-44,0, 40,-44,0, 41,-44,0, 42,-44,0, 43,-44,0,  /*[178]*/ /*[41.]*/
	          0,0,0,0,
	44,1,45,45, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,45,0, 1,-45,0, 2,-45,0, 3,-45,0, 4,-45,0, 5,-45,0, 6,-45,0, 7,-45,0, 8,-45,0, 9,-45,0, 10,-45,0, 11,-45,0, 12,-45,0, 13,-45,0, 14,-45,0, 15,-45,0, 16,-45,0, 17,-45,0, 18,-45,0, 19,-45,0, 20,-45,0, 21,-45,0, 22,-45,0, 23,-45,0, 24,-45,0, 25,-45,0, 26,-45,0, 27,-45,0, 28,-45,0, 29,-45,0, 30,-45,0, 31,-45,0, 32,-45,0, 33,-45,0, 34,-45,0, 35,-45,0, 36,-45,0, 37,-45,0, 38,-45,0, 39,-45,0, 40,-45,0, 41,-45,0, 42,-45,0, 43,-45,0, 44,-45,0,  /*[182]*/ /*[42.]*/
	          0,0,0,0,
	45,1,46,46, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,46,0, 1,-46,0, 2,-46,0, 3,-46,0, 4,-46,0, 5,-46,0, 6,-46,0, 7,-46,0, 8,-46,0, 9,-46,0, 10,-46,0, 11,-46,0, 12,-46,0, 13,-46,0, 14,-46,0, 15,-46,0, 16,-46,0, 17,-46,0, 18,-46,0, 19,-46,0, 20,-46,0, 21,-46,0, 22,-46,0, 23,-46,0, 24,-46,0, 25,-46,0, 26,-46,0, 27,-46,0, 28,-46,0, 29,-46,0, 30,-46,0, 31,-46,0, 32,-46,0, 33,-46,0, 34,-46,0, 35,-46,0, 36,-46,0, 37,-46,0, 38,-46,0, 39,-46,0, 40,-46,0, 41,-46,0, 42,-46,0, 43,-46,0, 44,-46,0, 45,-46,0,  /*[186]*/ /*[43.]*/
	          0,0,0,0,
	46,1,47,47, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,47,0, 1,-47,0, 2,-47,0, 3,-47,0, 4,-47,0, 5,-47,0, 6,-47,0, 7,-47,0, 8,-47,0, 9,-47,0, 10,-47,0, 11,-47,0, 12,-47,0, 13,-47,0, 14,-47,0, 15,-47,0, 16,-47,0, 17,-47,0, 18,-47,0, 19,-47,0, 20,-47,0, 21,-47,0, 22,-47,0, 23,-47,0, 24,-47,0, 25,-47,0, 26,-47,0, 27,-47,0, 28,-47,0, 29,-47,0, 30,-47,0, 31,-47,0, 32,-47,0, 33,-47,0, 34,-47,0, 35,-47,0, 36,-47,0, 37,-47,0, 38,-47,0, 39,-47,0, 40,-47,0, 41,-47,0, 42,-47,0, 43,-47,0, 44,-47,0, 45,-47,0, 46,-47,0,  /*[190]*/ /*[44.]*/
	          0,0,0,0,
	47,1,48,48, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,48,0, 1,-48,0, 2,-48,0, 3,-48,0, 4,-48,0, 5,-48,0, 6,-48,0, 7,-48,0, 8,-48,0, 9,-48,0, 10,-48,0, 11,-48,0, 12,-48,0, 13,-48,0, 14,-48,0, 15,-48,0, 16,-48,0, 17,-48,0, 18,-48,0, 19,-48,0, 20,-48,0, 21,-48,0, 22,-48,0, 23,-48,0, 24,-48,0, 25,-48,0, 26,-48,0, 27,-48,0, 28,-48,0, 29,-48,0, 30,-48,0, 31,-48,0, 32,-48,0, 33,-48,0, 34,-48,0, 35,-48,0, 36,-48,0, 37,-48,0, 38,-48,0, 39,-48,0, 40,-48,0, 41,-48,0, 42,-48,0, 43,-48,0, 44,-48,0, 45,-48,0, 46,-48,0, 47,-48,0,  /*[194]*/ /*[45.]*/
	          0,0,0,0,
	48,1,49,49, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,49,0, 1,-49,0, 2,-49,0, 3,-49,0, 4,-49,0, 5,-49,0, 6,-49,0, 7,-49,0, 8,-49,0, 9,-49,0, 10,-49,0, 11,-49,0, 12,-49,0, 13,-49,0, 14,-49,0, 15,-49,0, 16,-49,0, 17,-49,0, 18,-49,0, 19,-49,0, 20,-49,0, 21,-49,0, 22,-49,0, 23,-49,0, 24,-49,0, 25,-49,0, 26,-49,0, 27,-49,0, 28,-49,0, 29,-49,0, 30,-49,0, 31,-49,0, 32,-49,0, 33,-49,0, 34,-49,0, 35,-49,0, 36,-49,0, 37,-49,0, 38,-49,0, 39,-49,0, 40,-49,0, 41,-49,0, 42,-49,0, 43,-49,0, 44,-49,0, 45,-49,0, 46,-49,0, 47,-49,0, 48,-49,0,  /*[198]*/ /*[46.]*/
	          0,0,0,0,
	49,1,50,50, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,50,0, 1,-50,0, 2,-50,0, 3,-50,0, 4,-50,0, 5,-50,0, 6,-50,0, 7,-50,0, 8,-50,0, 9,-50,0, 10,-50,0, 11,-50,0, 12,-50,0, 13,-50,0, 14,-50,0, 15,-50,0, 16,-50,0, 17,-50,0, 18,-50,0, 19,-50,0, 20,-50,0, 21,-50,0, 22,-50,0, 23,-50,0, 24,-50,0, 25,-50,0, 26,-50,0, 27,-50,0, 28,-50,0, 29,-50,0, 30,-50,0, 31,-50,0, 32,-50,0, 33,-50,0, 34,-50,0, 35,-50,0, 36,-50,0, 37,-50,0, 38,-50,0, 39,-50,0, 40,-50,0, 41,-50,0, 42,-50,0, 43,-50,0, 44,-50,0, 45,-50,0, 46,-50,0, 47,-50,0, 48,-50,0, 49,-50,0,  /*[202]*/ /*[47.]*/
	          0,0,0,0,
	50,1,51,51, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,51,0, 1,-51,0, 2,-51,0, 3,-51,0, 4,-51,0, 5,-51,0, 6,-51,0, 7,-51,0, 8,-51,0, 9,-51,0, 10,-51,0, 11,-51,0, 12,-51,0, 13,-51,0, 14,-51,0, 15,-51,0, 16,-51,0, 17,-51,0, 18,-51,0, 19,-51,0, 20,-51,0, 21,-51,0, 22,-51,0, 23,-51,0, 24,-51,0, 25,-51,0, 26,-51,0, 27,-51,0, 28,-51,0, 29,-51,0, 30,-51,0, 31,-51,0, 32,-51,0, 33,-51,0, 34,-51,0, 35,-51,0, 36,-51,0, 37,-51,0, 38,-51,0, 39,-51,0, 40,-51,0, 41,-51,0, 42,-51,0, 43,-51,0, 44,-51,0, 45,-51,0, 46,-51,0, 47,-51,0, 48,-51,0, 49,-51,0, 50,-51,0,  /*[206]*/ /*[48.]*/
	          0,0,0,0,
	51,1,52,52, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,52,0, 1,-52,0, 2,-52,0, 3,-52,0, 4,-52,0, 5,-52,0, 6,-52,0, 7,-52,0, 8,-52,0, 9,-52,0, 10,-52,0, 11,-52,0, 12,-52,0, 13,-52,0, 14,-52,0, 15,-52,0, 16,-52,0, 17,-52,0, 18,-52,0, 19,-52,0, 20,-52,0, 21,-52,0, 22,-52,0, 23,-52,0, 24,-52,0, 25,-52,0, 26,-52,0, 27,-52,0, 28,-52,0, 29,-52,0, 30,-52,0, 31,-52,0, 32,-52,0, 33,-52,0, 34,-52,0, 35,-52,0, 36,-52,0, 37,-52,0, 38,-52,0, 39,-52,0, 40,-52,0, 41,-52,0, 42,-52,0, 43,-52,0, 44,-52,0, 45,-52,0, 46,-52,0, 47,-52,0, 48,-52,0, 49,-52,0, 50,-52,0, 51,-52,0,  /*[210]*/ /*[49.]*/
	          0,0,0,0,
	52,1,53,53, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,53,0, 1,-53,0, 2,-53,0, 3,-53,0, 4,-53,0, 5,-53,0, 6,-53,0, 7,-53,0, 8,-53,0, 9,-53,0, 10,-53,0, 11,-53,0, 12,-53,0, 13,-53,0, 14,-53,0, 15,-53,0, 16,-53,0, 17,-53,0, 18,-53,0, 19,-53,0, 20,-53,0, 21,-53,0, 22,-53,0, 23,-53,0, 24,-53,0, 25,-53,0, 26,-53,0, 27,-53,0, 28,-53,0, 29,-53,0, 30,-53,0, 31,-53,0, 32,-53,0, 33,-53,0, 34,-53,0, 35,-53,0, 36,-53,0, 37,-53,0, 38,-53,0, 39,-53,0, 40,-53,0, 41,-53,0, 42,-53,0, 43,-53,0, 44,-53,0, 45,-53,0, 46,-53,0, 47,-53,0, 48,-53,0, 49,-53,0, 50,-53,0, 51,-53,0, 52,-53,0,  /*[214]*/ /*[50.]*/
	          0,0,0,0,
	53,1,54,54, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,54,0, 1,-54,0, 2,-54,0, 3,-54,0, 4,-54,0, 5,-54,0, 6,-54,0, 7,-54,0, 8,-54,0, 9,-54,0, 10,-54,0, 11,-54,0, 12,-54,0, 13,-54,0, 14,-54,0, 15,-54,0, 16,-54,0, 17,-54,0, 18,-54,0, 19,-54,0, 20,-54,0, 21,-54,0, 22,-54,0, 23,-54,0, 24,-54,0, 25,-54,0, 26,-54,0, 27,-54,0, 28,-54,0, 29,-54,0, 30,-54,0, 31,-54,0, 32,-54,0, 33,-54,0, 34,-54,0, 35,-54,0, 36,-54,0, 37,-54,0, 38,-54,0, 39,-54,0, 40,-54,0, 41,-54,0, 42,-54,0, 43,-54,0, 44,-54,0, 45,-54,0, 46,-54,0, 47,-54,0, 48,-54,0, 49,-54,0, 50,-54,0, 51,-54,0, 52,-54,0, 53,-54,0,  /*[218]*/ /*[51.]*/
	          0,0,0,0,
	54,1,55,55, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,-54,55,0, 1,-55,0, 2,-55,0, 3,-55,0, 4,-55,0, 5,-55,0, 6,-55,0, 7,-55,0, 8,-55,0, 9,-55,0, 10,-55,0, 11,-55,0, 12,-55,0, 13,-55,0, 14,-55,0, 15,-55,0, 16,-55,0, 17,-55,0, 18,-55,0, 19,-55,0, 20,-55,0, 21,-55,0, 22,-55,0, 23,-55,0, 24,-55,0, 25,-55,0, 26,-55,0, 27,-55,0, 28,-55,0, 29,-55,0, 30,-55,0, 31,-55,0, 32,-55,0, 33,-55,0, 34,-55,0, 35,-55,0, 36,-55,0, 37,-55,0, 38,-55,0, 39,-55,0, 40,-55,0, 41,-55,0, 42,-55,0, 43,-55,0, 44,-55,0, 45,-55,0, 46,-55,0, 47,-55,0, 48,-55,0, 49,-55,0, 50,-55,0, 51,-55,0, 52,-55,0, 53,-55,0, 54,-55,0,  /*[222]*/ /*[52.]*/
	          0,0,0,0,
	55,1,56,56, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,-54,-55,56,0, 1,-56,0, 2,-56,0, 3,-56,0, 4,-56,0, 5,-56,0, 6,-56,0, 7,-56,0, 8,-56,0, 9,-56,0, 10,-56,0, 11,-56,0, 12,-56,0, 13,-56,0, 14,-56,0, 15,-56,0, 16,-56,0, 17,-56,0, 18,-56,0, 19,-56,0, 20,-56,0, 21,-56,0, 22,-56,0, 23,-56,0, 24,-56,0, 25,-56,0, 26,-56,0, 27,-56,0, 28,-56,0, 29,-56,0, 30,-56,0, 31,-56,0, 32,-56,0, 33,-56,0, 34,-56,0, 35,-56,0, 36,-56,0, 37,-56,0, 38,-56,0, 39,-56,0, 40,-56,0, 41,-56,0, 42,-56,0, 43,-56,0, 44,-56,0, 45,-56,0, 46,-56,0, 47,-56,0, 48,-56,0, 49,-56,0, 50,-56,0, 51,-56,0, 52,-56,0, 53,-56,0, 54,-56,0, 55,-56,0,  /*[226]*/ /*[53.]*/
	          0,0,0,0,
	56,1,57,57, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,-54,-55,-56,57,0, 1,-57,0, 2,-57,0, 3,-57,0, 4,-57,0, 5,-57,0, 6,-57,0, 7,-57,0, 8,-57,0, 9,-57,0, 10,-57,0, 11,-57,0, 12,-57,0, 13,-57,0, 14,-57,0, 15,-57,0, 16,-57,0, 17,-57,0, 18,-57,0, 19,-57,0, 20,-57,0, 21,-57,0, 22,-57,0, 23,-57,0, 24,-57,0, 25,-57,0, 26,-57,0, 27,-57,0, 28,-57,0, 29,-57,0, 30,-57,0, 31,-57,0, 32,-57,0, 33,-57,0, 34,-57,0, 35,-57,0, 36,-57,0, 37,-57,0, 38,-57,0, 39,-57,0, 40,-57,0, 41,-57,0, 42,-57,0, 43,-57,0, 44,-57,0, 45,-57,0, 46,-57,0, 47,-57,0, 48,-57,0, 49,-57,0, 50,-57,0, 51,-57,0, 52,-57,0, 53,-57,0, 54,-57,0, 55,-57,0, 56,-57,0,  /*[230]*/ /*[54.]*/
	          0,0,0,0,
	57,1,58,58, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,-54,-55,-56,-57,58,0, 1,-58,0, 2,-58,0, 3,-58,0, 4,-58,0, 5,-58,0, 6,-58,0, 7,-58,0, 8,-58,0, 9,-58,0, 10,-58,0, 11,-58,0, 12,-58,0, 13,-58,0, 14,-58,0, 15,-58,0, 16,-58,0, 17,-58,0, 18,-58,0, 19,-58,0, 20,-58,0, 21,-58,0, 22,-58,0, 23,-58,0, 24,-58,0, 25,-58,0, 26,-58,0, 27,-58,0, 28,-58,0, 29,-58,0, 30,-58,0, 31,-58,0, 32,-58,0, 33,-58,0, 34,-58,0, 35,-58,0, 36,-58,0, 37,-58,0, 38,-58,0, 39,-58,0, 40,-58,0, 41,-58,0, 42,-58,0, 43,-58,0, 44,-58,0, 45,-58,0, 46,-58,0, 47,-58,0, 48,-58,0, 49,-58,0, 50,-58,0, 51,-58,0, 52,-58,0, 53,-58,0, 54,-58,0, 55,-58,0, 56,-58,0, 57,-58,0,  /*[234]*/ /*[55.]*/
	          0,0,0,0,
	58,1,59,59, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,-54,-55,-56,-57,-58,59,0, 1,-59,0, 2,-59,0, 3,-59,0, 4,-59,0, 5,-59,0, 6,-59,0, 7,-59,0, 8,-59,0, 9,-59,0, 10,-59,0, 11,-59,0, 12,-59,0, 13,-59,0, 14,-59,0, 15,-59,0, 16,-59,0, 17,-59,0, 18,-59,0, 19,-59,0, 20,-59,0, 21,-59,0, 22,-59,0, 23,-59,0, 24,-59,0, 25,-59,0, 26,-59,0, 27,-59,0, 28,-59,0, 29,-59,0, 30,-59,0, 31,-59,0, 32,-59,0, 33,-59,0, 34,-59,0, 35,-59,0, 36,-59,0, 37,-59,0, 38,-59,0, 39,-59,0, 40,-59,0, 41,-59,0, 42,-59,0, 43,-59,0, 44,-59,0, 45,-59,0, 46,-59,0, 47,-59,0, 48,-59,0, 49,-59,0, 50,-59,0, 51,-59,0, 52,-59,0, 53,-59,0, 54,-59,0, 55,-59,0, 56,-59,0, 57,-59,0, 58,-59,0,  /*[238]*/ /*[56.]*/
	          0,0,0,0,
	59,1,60,60, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,-54,-55,-56,-57,-58,-59,60,0, 1,-60,0, 2,-60,0, 3,-60,0, 4,-60,0, 5,-60,0, 6,-60,0, 7,-60,0, 8,-60,0, 9,-60,0, 10,-60,0, 11,-60,0, 12,-60,0, 13,-60,0, 14,-60,0, 15,-60,0, 16,-60,0, 17,-60,0, 18,-60,0, 19,-60,0, 20,-60,0, 21,-60,0, 22,-60,0, 23,-60,0, 24,-60,0, 25,-60,0, 26,-60,0, 27,-60,0, 28,-60,0, 29,-60,0, 30,-60,0, 31,-60,0, 32,-60,0, 33,-60,0, 34,-60,0, 35,-60,0, 36,-60,0, 37,-60,0, 38,-60,0, 39,-60,0, 40,-60,0, 41,-60,0, 42,-60,0, 43,-60,0, 44,-60,0, 45,-60,0, 46,-60,0, 47,-60,0, 48,-60,0, 49,-60,0, 50,-60,0, 51,-60,0, 52,-60,0, 53,-60,0, 54,-60,0, 55,-60,0, 56,-60,0, 57,-60,0, 58,-60,0, 59,-60,0,  /*[242]*/ /*[57.]*/
	          0,0,0,0,
	60,1,61,61, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,-54,-55,-56,-57,-58,-59,-60,61,0, 1,-61,0, 2,-61,0, 3,-61,0, 4,-61,0, 5,-61,0, 6,-61,0, 7,-61,0, 8,-61,0, 9,-61,0, 10,-61,0, 11,-61,0, 12,-61,0, 13,-61,0, 14,-61,0, 15,-61,0, 16,-61,0, 17,-61,0, 18,-61,0, 19,-61,0, 20,-61,0, 21,-61,0, 22,-61,0, 23,-61,0, 24,-61,0, 25,-61,0, 26,-61,0, 27,-61,0, 28,-61,0, 29,-61,0, 30,-61,0, 31,-61,0, 32,-61,0, 33,-61,0, 34,-61,0, 35,-61,0, 36,-61,0, 37,-61,0, 38,-61,0, 39,-61,0, 40,-61,0, 41,-61,0, 42,-61,0, 43,-61,0, 44,-61,0, 45,-61,0, 46,-61,0, 47,-61,0, 48,-61,0, 49,-61,0, 50,-61,0, 51,-61,0, 52,-61,0, 53,-61,0, 54,-61,0, 55,-61,0, 56,-61,0, 57,-61,0, 58,-61,0, 59,-61,0, 60,-61,0,  /*[246]*/ /*[58.]*/
	          0,0,0,0,
	61,1,62,62, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,-54,-55,-56,-57,-58,-59,-60,-61,62,0, 1,-62,0, 2,-62,0, 3,-62,0, 4,-62,0, 5,-62,0, 6,-62,0, 7,-62,0, 8,-62,0, 9,-62,0, 10,-62,0, 11,-62,0, 12,-62,0, 13,-62,0, 14,-62,0, 15,-62,0, 16,-62,0, 17,-62,0, 18,-62,0, 19,-62,0, 20,-62,0, 21,-62,0, 22,-62,0, 23,-62,0, 24,-62,0, 25,-62,0, 26,-62,0, 27,-62,0, 28,-62,0, 29,-62,0, 30,-62,0, 31,-62,0, 32,-62,0, 33,-62,0, 34,-62,0, 35,-62,0, 36,-62,0, 37,-62,0, 38,-62,0, 39,-62,0, 40,-62,0, 41,-62,0, 42,-62,0, 43,-62,0, 44,-62,0, 45,-62,0, 46,-62,0, 47,-62,0, 48,-62,0, 49,-62,0, 50,-62,0, 51,-62,0, 52,-62,0, 53,-62,0, 54,-62,0, 55,-62,0, 56,-62,0, 57,-62,0, 58,-62,0, 59,-62,0, 60,-62,0, 61,-62,0,  /*[250]*/ /*[59.]*/
	          0,0,0,0,
	62,1,63,63, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,-54,-55,-56,-57,-58,-59,-60,-61,-62,63,0, 1,-63,0, 2,-63,0, 3,-63,0, 4,-63,0, 5,-63,0, 6,-63,0, 7,-63,0, 8,-63,0, 9,-63,0, 10,-63,0, 11,-63,0, 12,-63,0, 13,-63,0, 14,-63,0, 15,-63,0, 16,-63,0, 17,-63,0, 18,-63,0, 19,-63,0, 20,-63,0, 21,-63,0, 22,-63,0, 23,-63,0, 24,-63,0, 25,-63,0, 26,-63,0, 27,-63,0, 28,-63,0, 29,-63,0, 30,-63,0, 31,-63,0, 32,-63,0, 33,-63,0, 34,-63,0, 35,-63,0, 36,-63,0, 37,-63,0, 38,-63,0, 39,-63,0, 40,-63,0, 41,-63,0, 42,-63,0, 43,-63,0, 44,-63,0, 45,-63,0, 46,-63,0, 47,-63,0, 48,-63,0, 49,-63,0, 50,-63,0, 51,-63,0, 52,-63,0, 53,-63,0, 54,-63,0, 55,-63,0, 56,-63,0, 57,-63,0, 58,-63,0, 59,-63,0, 60,-63,0, 61,-63,0, 62,-63,0,  /*[254]*/ /*[60.]*/
	          0,0,0,0,
	63,1,64,64, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,-54,-55,-56,-57,-58,-59,-60,-61,-62,-63,64,0, 1,-64,0, 2,-64,0, 3,-64,0, 4,-64,0, 5,-64,0, 6,-64,0, 7,-64,0, 8,-64,0, 9,-64,0, 10,-64,0, 11,-64,0, 12,-64,0, 13,-64,0, 14,-64,0, 15,-64,0, 16,-64,0, 17,-64,0, 18,-64,0, 19,-64,0, 20,-64,0, 21,-64,0, 22,-64,0, 23,-64,0, 24,-64,0, 25,-64,0, 26,-64,0, 27,-64,0, 28,-64,0, 29,-64,0, 30,-64,0, 31,-64,0, 32,-64,0, 33,-64,0, 34,-64,0, 35,-64,0, 36,-64,0, 37,-64,0, 38,-64,0, 39,-64,0, 40,-64,0, 41,-64,0, 42,-64,0, 43,-64,0, 44,-64,0, 45,-64,0, 46,-64,0, 47,-64,0, 48,-64,0, 49,-64,0, 50,-64,0, 51,-64,0, 52,-64,0, 53,-64,0, 54,-64,0, 55,-64,0, 56,-64,0, 57,-64,0, 58,-64,0, 59,-64,0, 60,-64,0, 61,-64,0, 62,-64,0, 63,-64,0,  /*[258]*/ /*[61.]*/
	          0,0,0,0,
	64,1,65,65, -1,-2,-3,-4,-5,-6,-7,-8,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-27,-28,-29,-30,-31,-32,-33,-34,-35,-36,-37,-38,-39,-40,-41,-42,-43,-44,-45,-46,-47,-48,-49,-50,-51,-52,-53,-54,-55,-56,-57,-58,-59,-60,-61,-62,-63,-64,65,0, 1,-65,0, 2,-65,0, 3,-65,0, 4,-65,0, 5,-65,0, 6,-65,0, 7,-65,0, 8,-65,0, 9,-65,0, 10,-65,0, 11,-65,0, 12,-65,0, 13,-65,0, 14,-65,0, 15,-65,0, 16,-65,0, 17,-65,0, 18,-65,0, 19,-65,0, 20,-65,0, 21,-65,0, 22,-65,0, 23,-65,0, 24,-65,0, 25,-65,0, 26,-65,0, 27,-65,0, 28,-65,0, 29,-65,0, 30,-65,0, 31,-65,0, 32,-65,0, 33,-65,0, 34,-65,0, 35,-65,0, 36,-65,0, 37,-65,0, 38,-65,0, 39,-65,0, 40,-65,0, 41,-65,0, 42,-65,0, 43,-65,0, 44,-65,0, 45,-65,0, 46,-65,0, 47,-65,0, 48,-65,0, 49,-65,0, 50,-65,0, 51,-65,0, 52,-65,0, 53,-65,0, 54,-65,0, 55,-65,0, 56,-65,0, 57,-65,0, 58,-65,0, 59,-65,0, 60,-65,0, 61,-65,0, 62,-65,0, 63,-65,0, 64,-65,0,  /*[262]*/ /*[62.]*/
} ;

    /* index into cnf_and_template_ints */
static const struct TemplIndex cnf_and_templ_ints_idx[ 63 ] = {
	{    0,  14 },  /*[ 0]*/
	{   18,  18 },  /*[ 1]*/
	{   40,  22 },  /*[ 2]*/
	{   66,  26 },  /*[ 3]*/
	{   96,  30 },  /*[ 4]*/
	{  130,  34 },  /*[ 5]*/
	{  168,  38 },  /*[ 6]*/
	{  210,  42 },  /*[ 7]*/
	{  256,  46 },  /*[ 8]*/
	{  306,  50 },  /*[ 9]*/
	{  360,  54 },  /*[10]*/
	{  418,  58 },  /*[11]*/
	{  480,  62 },  /*[12]*/
	{  546,  66 },  /*[13]*/
	{  616,  70 },  /*[14]*/
	{  690,  74 },  /*[15]*/
	{  768,  78 },  /*[16]*/
	{  850,  82 },  /*[17]*/
	{  936,  86 },  /*[18]*/
	{ 1026,  90 },  /*[19]*/
	{ 1120,  94 },  /*[20]*/
	{ 1218,  98 },  /*[21]*/
	{ 1320, 102 },  /*[22]*/
	{ 1426, 106 },  /*[23]*/
	{ 1536, 110 },  /*[24]*/
	{ 1650, 114 },  /*[25]*/
	{ 1768, 118 },  /*[26]*/
	{ 1890, 122 },  /*[27]*/
	{ 2016, 126 },  /*[28]*/
	{ 2146, 130 },  /*[29]*/
	{ 2280, 134 },  /*[30]*/
	{ 2418, 138 },  /*[31]*/
	{ 2560, 142 },  /*[32]*/
	{ 2706, 146 },  /*[33]*/
	{ 2856, 150 },  /*[34]*/
	{ 3010, 154 },  /*[35]*/
	{ 3168, 158 },  /*[36]*/
	{ 3330, 162 },  /*[37]*/
	{ 3496, 166 },  /*[38]*/
	{ 3666, 170 },  /*[39]*/
	{ 3840, 174 },  /*[40]*/
	{ 4018, 178 },  /*[41]*/
	{ 4200, 182 },  /*[42]*/
	{ 4386, 186 },  /*[43]*/
	{ 4576, 190 },  /*[44]*/
	{ 4770, 194 },  /*[45]*/
	{ 4968, 198 },  /*[46]*/
	{ 5170, 202 },  /*[47]*/
	{ 5376, 206 },  /*[48]*/
	{ 5586, 210 },  /*[49]*/
	{ 5800, 214 },  /*[50]*/
	{ 6018, 218 },  /*[51]*/
	{ 6240, 222 },  /*[52]*/
	{ 6466, 226 },  /*[53]*/
	{ 6696, 230 },  /*[54]*/
	{ 6930, 234 },  /*[55]*/
	{ 7168, 238 },  /*[56]*/
	{ 7410, 242 },  /*[57]*/
	{ 7656, 246 },  /*[58]*/
	{ 7906, 250 },  /*[59]*/
	{ 8160, 254 },  /*[60]*/
	{ 8418, 258 },  /*[61]*/
	{ 8680, 262 },  /*[62]*/
} ;

#endif  /* !def(CNF_AND_TEMPLATE_H__) */
