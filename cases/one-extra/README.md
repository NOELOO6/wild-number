# One extra edge for every K15 through K82

Let b = ⌊4⌈n/2⌉/3⌋. Every minimum proper coloring in this range has wild number b or b+1. The universal lower bound is proved separately. [Upper bound](NearRange.lean) · [Lower bound](../../verification/exact/UniversalLower.lean)

| Orders | Lower bound | Upper bound |
| --- | ---: | ---: |
| K19, K20 | 13 | 14 |
| K23, K24 | 16 | 17 |
| K27, K28 | 18 | 19 |
| K79, K80 | 53 | 54 |
| K81, K82 | 54 | 55 |

For odd n, put 3, 4 or 5 vertices in one distinguished group and split the remaining vertices into triples. Join each group by a star. A cut is a division of the vertices into two nonempty sides. It obstructs a color when no star edge and no edge of that color crosses the division.

Count each cut by its side outside the distinguished group. If that side consists of j triples, it has 3j vertices. Each color pairs all but one of the n vertices. Parity determines whether the unmatched vertex belongs to the side, so the possible sides of the correct size are counted by a single binomial coefficient. Summing over j gives an average of fewer than three obstructing cuts across all colors at each certified odd order. Some placement therefore has at most two. [Compressed count](NearCharge.lean) · [Permutation bound](../../verification/graph-bounds/UniformCuts.lean)

Any two nontrivial cuts admit an edge that crosses both. Adding that edge connects every color, using at most b+1 wild edges. The proof also transfers this bound to each following even order. [Repair argument](../../verification/graph-bounds/CutRepair.lean) · [Graph theorem](NearRange.lean)

Run `./verification/graph-bounds.sh one-extra` with Lean 4.19.0. The ordinary kernel checks the proof and the finite arithmetic.
