# Optimal layouts under simultaneous alternating-cycle switches

One fixed set of wild edges attains the conjectured value throughout each family below. The construction covers every unresolved order from K₁₅ through K₇₆. The exponents count distinct colorings on fixed vertex labels. Each odd order and its following even order have the same guarantee.

| Orders | Colorings, at least | Orders | Colorings, at least | Orders | Colorings, at least |
| --- | ---: | --- | ---: | --- | ---: |
| 15–16 | 2¹⁶ | 37–38 | 2⁷⁸ | 57–58 | 2¹⁸⁹ |
| 19–20 | 2³² | 39–40 | 2¹⁰⁴ | 59–60 | 2²³⁶ |
| 21–22 | 2²³ | 41–42 | 2¹¹⁰ | 61–62 | 2²¹⁷ |
| 23–24 | 2³⁸ | 43–44 | 2¹⁷⁰ | 63–64 | 2²⁵⁵ |
| 25–26 | 2³⁶ | 45–46 | 2¹¹² | 65–66 | 2²⁶⁹ |
| 27–28 | 2⁵² | 47–48 | 2¹⁵² | 67–68 | 2⁴⁰⁵ |
| 29–30 | 2⁵³ | 49–50 | 2¹³⁴ | 69–70 | 2²⁷⁶ |
| 31–32 | 2⁸⁸ | 51–52 | 2²⁰² | 71–72 | 2⁴²⁶ |
| 33–34 | 2⁶⁴ | 53–54 | 2¹⁷⁸ | 73–74 | 2³¹⁵ |
| 35–36 | 2⁸⁶ | 55–56 | 2²⁷³ | 75–76 | 2³⁵⁹ |

## Construction

Start on $2m=n+1$ vertices with a one-factorization on two equal layers. Each layer uses the round-robin matchings. At odd layer size the second layer first reverses the even positions. The remaining cross-layer matchings use cyclic shifts. The certificate gives a partition of the ordinary vertices and a list of disjoint color pairs. Draw a star in each ordinary block and leave the last vertex as a singleton. The displayed stars use $(2n+2)\mathbin{/}3$ edges with integer division. [Partner construction](CycleFamilies.lean) · [Layouts and color pairs](families.jsonl)

The union of two paired colors decomposes into even alternating cycles. On each cycle choose independently which alternating half is assigned to the first color. The other color receives the complementary half. This preserves the one-factorization, and disjoint palette pairs can be switched independently. If a pair has $h$ cycles, fixing the choice on its first cycle leaves $2^{h-1}$ possibilities. This removes the interchange of the two whole color names. Distinct choices give different colorings even after deleting the singleton, because a cycle has at least four vertices and has ordinary edges of both parities.

## Connectivity and verification

For one color at a time, start with the connected components of the wild edges. Each cycle offers two sets of edges. Merge components along either set, keep each distinct resulting component partition once, and discard partitions that are already connected. An empty list at the end proves that every orientation connects the graph. Lean proves this implication for arbitrary menus and any proper coloring realizing them. The 30 rows check both the odd and the even graph separately. The general lower bound gives equality. The finite checks use Lean's native evaluator. [Soundness proof](SwitchFamily.lean) · [End-to-end theorem](CycleCertificates.lean)

Run `python3 cases/regrouping/cycle-families/check.py` from the repository root for an independent check with the standard library. A single odd order can be supplied as an argument. Run `./verification/graph-bounds.sh regrouping` for the Lean proofs.
