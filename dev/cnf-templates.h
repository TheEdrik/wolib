#if !defined(CNF_TEMPLATES_H__)
#define  CNF_TEMPLATES_H__  1

/* common template-related definitions (include with binary distributions) */

struct TemplIndex {
	unsigned int offset;
	unsigned int count;
} ;

/* N-bit clause-annotation definitions
 */
#if !defined(CNF_VAR_IS_NEGATED8)
#define  CNF_VAR_IS_NEGATED8  UINT8_C(0x80)
#endif
/**/
#if !defined(CNF_VAR_IS_CLAUSE_END8)
#define  CNF_VAR_IS_CLAUSE_END8  UINT8_C(0x40)
#endif
/**/
#if !defined(CNF_VAR_IS_ADDED8)
#define  CNF_VAR_IS_ADDED8  UINT8_C(0x20)
#endif
/**/
#if !defined(CNF_VAR_MASK8)
#define  CNF_VAR_MASK8  UINT8_C(0x1f)
#endif

#if !defined(CNF_VAR_IS_NEGATED16)
#define  CNF_VAR_IS_NEGATED16  UINT16_C(0x8000)
#endif
/**/
#if !defined(CNF_VAR_IS_CLAUSE_END16)
#define  CNF_VAR_IS_CLAUSE_END16  UINT16_C(0x4000)
#endif
/**/
#if !defined(CNF_VAR_IS_ADDED16)
#define  CNF_VAR_IS_ADDED16  UINT16_C(0x2000)
#endif
/**/
#if !defined(CNF_VAR_MASK16)
#define  CNF_VAR_MASK16  UINT16_C(0x1fff)
#endif

#endif    /* !defined(CNF_TEMPLATES_H__) */

