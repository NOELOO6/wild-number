# Two rings of seven

**Ten wild lines work for every fifteen-point coloring with a symmetry of order seven.** A symmetry here may relabel the colors as it moves the points. The proof covers 797,448 compatible pairs of labeled starting patterns. Some pairs describe copies of the same coloring.

## Build the coloring

Put seven points on ring A, seven on ring B and one in the middle. The symmetry turns both rings by one step. Add an auxiliary sixteenth point outside the rings. Join it to each point in the color that was missing at that point. Each color now pairs up all sixteen points.

Every symmetry of order seven on fifteen points has either one or two moving rings. A single moving ring cannot occur. Choose a fixed point and consider the color missing there. This color would have to pair the seven moving points among themselves, since their partners move with them. Seven is odd. Thus there are two rings and one fixed point.

The color missing at the middle is fixed. It pairs the two fixed points and pairs ring A with ring B. A whole ring cannot be paired with itself because it has odd size. Relabel the second ring so that these seven pairs are aligned. All remaining colors fall into two sets of seven. Pick the one missing at A₀ and the one missing at B₀. Rotating these two starters gives all fourteen colors.

The aligned fixed matching leaves sixteen groups of edges that rotate together. Each starter must use eight different groups. The two starters must use complementary groups. Conversely, every such pair uses every edge of the complete graph exactly once after developing the two starters. These observations justify the reduction to the enumeration.

## Check the ten lines

Each candidate grouping splits the fifteen points into five triples. Draw two wild lines inside each triple so its three points can reach each other. A color connects everything precisely when it crosses every cut between whole triples. With five triples, one side of any nontrivial cut contains either one or two triples. This gives just fifteen cut tests per color.

| What was counted | Number |
| --- | ---: |
| Starters based at A₀ | 19,876 |
| Starters based at B₀ | 19,876 |
| Compatible labeled pairs | 797,448 |
| Candidate groupings in the certificate | 71 |
| Compatible pairs left without a solution | **0** |

Lean forms all starters recursively by pairing the least unused point. It verifies the groupings, checks all rotated cuts and proves that every compatible pair has a working grouping. The symmetry reduction above is a written argument. The independent Python check uses a second criterion. It lists point sets that a matching stays inside, then checks that a proposed grouping uses none of them. [Lean theorem](Seven.lean) · [Independent checker](check_seven.py)
