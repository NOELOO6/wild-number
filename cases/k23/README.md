# Cyclic colorings of K23

A minimum proper coloring of K23 has wild number 16 whenever it admits a 23-cycle permuting its color classes. The same value holds for a minimum coloring of K24 if deleting a vertex gives such a coloring. The unrestricted bounds at both orders are 16–17. [Graph theorems](Cyclic23.lean) · [General bounds](../one-extra/)

Label the cycle by the residues modulo 23. The color missing at zero pairs up the other 22 vertices. It uses each circular edge length exactly once. Edges of the same length are translates, and translating an edge of this color to another edge of this color would fix its unique missing vertex. Lean proves this reduction at arbitrary odd order. [Starter extraction](../../verification/exact/CyclicExtraction.lean)

The certificate lists 92 candidate vertex orders. Read each order as six triples followed by a group of five. Draw a star in each group, giving sixteen edges. For every starter, Lean checks that some order connects all 23 translated matchings. The checker records the group cuts crossed by each matching edge in a bit mask. A separate exhaustive count found 1,515,283 labeled starters. The Lean theorem depends on the exhaustive search and a proof that crossing every cut supplies paths, independent of this reported count. [Candidate orders and drawings](Starters23.lean) · [Exhaustive check](Cyclic23Check.lean) · [Path transport](../../verification/exact/RotationalLayouts.lean)

Run `./verification/graph-bounds.sh cyclic-k23` with Lean 4.19.0. This target uses Lean’s native evaluator.
