# Grouping the nine outside points on K15

Fix six ordinary points. Add a sixteenth point, the **root**, and join it to each ordinary point using the color missing there. Assume every color has at most two edges entirely inside the fixed six and the root. This is the seven-point rule.

**The other nine points always admit two partitions into triples that share no triple.** For either partition, every color crosses both of the following cuts for each of its triples T.

| Side of the cut | Number of points |
| --- | ---: |
| The root together with T | 4 |
| The six outside points left after removing T | 6 |

One may also prescribe up to four triples to avoid and still find a partition passing both tests. This holds for every proper coloring satisfying the rule, including changes to the edges among the nine. [Graph theorems](ExteriorGraph.lean)

## Consequences for wild edges

Joining the fixed six in a tree takes five wild edges. Joining each outside triple takes two. These **eleven edges connect all fifteen colors**, even when the four extra exclusions are imposed. The construction preserves the chosen six. [Graph and path proof](ExteriorRepair.lean)

For ten edges, split the fixed six into triples A and B. Each must pass its own root cut. Among outside triples that pass the two common tests, mark T if a color fails to cross A ∪ T or B ∪ T. If at most four such triples are marked, ten edges suffice. Whether every coloring admits a successful ten-edge layout remains open. [Cut classification](ResidualCuts.lean) · [Exact conditional theorem](ExteriorRepair.lean)

## Proof

There are 84 triples on the nine outside points. Block a triple if a color closes either common cut. Counting pairs and partners of the root gives these upper bounds.

| Blocked triples counted | Maximum |
| --- | ---: |
| All | 31 |
| Containing one specified point | 18 |
| Containing at least two points of a specified four | 24 |
| Contained in a specified seven | 22 |

Adding four arbitrary triples respects the limits 35, 23, 30 and 33 of the nine-point obstruction theorem used in the K13 proof. That theorem gives a partition avoiding all blocked triples. To obtain two partitions with no common triple, forbid the three triples of the first partition and apply the result again. [Per-color inequalities](ExteriorPrices.lean) · [Counts over all colors](ExteriorTotals.lean) · [Nine-point theorem applied to actual triples](ExteriorNine.lean)

Run `./verification/graph-bounds.sh exterior` from the repository root. It builds the pinned mathematical dependencies, regenerates the nine-point certificate and checks the correspondence between matching cuts, partitions and graph paths. The row enumeration and the certificate use Lean’s native evaluator.
