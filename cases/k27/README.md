# Cyclic colorings of K27

A minimum proper coloring of K27 with a 27-cycle permuting the color classes has wild number 18. A minimum coloring of K28 also has wild number 18 whenever a vertex deletion has this symmetry. At both orders the unrestricted bounds are 18–19. [Graph theorems](Cyclic27.lean) · [General bounds](../one-extra/)

In cyclic coordinates the color missing at zero matches the other 26 vertices, using each circular edge length exactly once. Multiplication by a unit modulo 27 gives another cyclic labeling. Choose a labeling that minimizes the numerical partner of 1. For every edge in the resulting starter, scaling either endpoint to 1 must give a partner at least as large. This observation discards branches before the other edges of the matching have been chosen. The normalization proof applies at any odd order greater than one. [Starter extraction](../../verification/exact/CyclicExtraction.lean) · [Normalization proof](../../verification/exact/CyclicNormal.lean)

For each pair of residues $a,b$ modulo 9, form the nine triples $\{3i,3(i+a)+1,3(i+b)+2\}$ modulo 27. A star on each triple gives eighteen wild edges. Translation by three preserves this drawing, so three matching translates suffice to test each of these 81 candidates. An independent enumeration found 9,820,074 normalized starters. Of those, 75 needed a different drawing. Five additional layouts cover them. Lean checks the full search and verifies that each accepted drawing gives paths in all 27 colors. [Candidate layouts](Starters27.lean) · [Exhaustive check](Cyclic27Check.lean) · [Cut test and soundness](../../verification/exact/CyclicCutSound.lean)

Run `./verification/graph-bounds.sh cyclic-k27` with Lean 4.19.0. The finite starter and drawing checks use Lean’s native evaluator.
