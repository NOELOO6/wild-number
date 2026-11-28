# Exact wild numbers from finite partition counts

At every order from K77 upward and at every multiple of six from 30 upward, every minimum proper edge coloring has wild number ⌊4⌈n/2⌉/3⌋. The interval proof treats the odd orders together. Deleting or adding one vertex transfers the result to the following even order. [All orders from 77](AllLarge.lean) · [Finite interval theorem](ExactInterval.lean) · [Odd/even transfer](../../verification/exact/UniversalLower.lean)

| Orders | Wild number |
| --- | ---: |
| K24 | [16, with written counting proof](../k24/) |
| K30 | [20](../k30/) |
| K36 | [24](../k36/) |
| K42 | 28 |
| K48, K54, K60, K66, K72 | 32, 36, 40, 44, 48 |
| K77, K78 | 52 |
| K79, K80 | 53 |
| K81, K82 | 54 |
| K83, K84 | 56 |
| K89, K90 | 60 |
| K91, K92 | 61 |
| K93, K94 | 62 |
| K153, K154 | 102 |

At each order n = 6s + 15, at least 10/91 of all partitions into triples have an edge of every color leaving each triple, for every minimum proper coloring. More generally, the same fraction avoids any family of forbidden triples in which at most three contain each pair of vertices. The theorem also gives an order-dependent count. If $W_t$ is the number of partitions of $3t$ points into triples, it guarantees $P(s)W_{2s+2}$ partitions, where $P(s)=15400+77118s+146688s^2+139374s^3+70848s^4+18468s^5+1944s^6$. Dividing by $W_{2s+5}$ gives a lower bound tending to one third as $s$ grows. This counts partitions that pass the first cut test. Unions of multiple triples can still be closed. [Uniform density theorem](UniformRootDensity.lean) · [Sharper finite counts](RootDensity.lean)

## Counting argument

Add one auxiliary vertex so that every color is a perfect matching. Set aside a small group whose internal edges have distinct colors, then partition the remaining vertices into triples. Within each group, draw a star of wild edges. A color fails to connect precisely when some nonempty proper union of groups has no matching edge crossing its boundary. [Choice of group](Rainbow.lean) · [Graph connectivity](GraphSieve.lean)

The proof first counts partitions avoiding every such cut involving one or two free triples on the smaller side. An inequality for forcing specified triples bounds the cost of excluding each cut. The degrees in this count use the fact that an edge belongs to exactly one color. A final sum bounds the number of surviving partitions lost to larger cuts. At each certified order this sum leaves at least one winning partition. [Partition comparison](TripleCoupling.lean) · [Local edge count](DegreeChord.lean) · [Existence argument](FrozenLayout.lean)

The proof uses the matching and random-partition approach of the separate large-order project. The finite comparison sequence and its order-by-order certificates are developed here. [Large-order proof](https://github.com/1337isnot1337/solved-conjectures/blob/main/results/wild-number-complete-graphs/IMPROVEMENT.md)

## Orders divisible by six

The original paper settles K6 and K12. Together with K18, the K24 counting proof and the infinite theorem starting at K30, this gives wild number 4m for every K₆ₘ, m ≥ 1. [Original paper](https://arxiv.org/html/2610.22142v1#S3.SS3) · [K18](../../verification/exact/K17K18.lean) · [K24](../k24/) · [Lean theorem starting at K30](SixFamily.lean)

At K48, K54, K60, K66 and K72 all vertices can be divided into triples. A color pairs up every vertex. A closed union of triples must therefore contain an even number of triples. The first possible obstruction has six vertices. When a cut divides the vertices equally, its two sides describe the same failure, so the count keeps the side avoiding one fixed point. The resulting inequalities leave a working grouping at all five orders. [Graph proof](EvenTriples.lean) · [Exact values](EvenOrders.lean)

The same construction proves that **K₆ₘ has wild number 4m for every m ≥ 5**, with no upper limit on m. Each of the 2m triples uses two wild edges. To show that at least one partition works, count the fraction of partitions lost to closed sets of each size. At m ≥ 14 their sum is less than one. Lean checks the integer inequalities for 14 ≤ m < 70. For all m ≥ 70 a recurrence bounds the sum by a decreasing sequence, starting with a term of size 5m/(6m−5). K30 bounds the joint distribution of marked sixes in a twelve-cut, and K36 counts three simultaneous six-point failures. [K30 proof](../k30/) · [K36 proof](../k36/)

The remaining small cases use the K42 overlap count, the stronger local count or the K78 theorem. [Term recurrence](EvenRatios.lean) · [Uniform estimate](EvenSeries.lean) · [Family beginning at K30](SixFamily.lean) · [Ordinary-kernel family beginning at K36](InfiniteEven.lean)

### Why 28 works on K42

Divide the 42 vertices into fourteen triples and choose two wild edges per triple. A color can disconnect this grouping only by closing a set of 6, 12 or 18 vertices on the smaller side. The proof counts the partitions lost to six-point sets first. Different closed sets can spoil the same partition, and counting that overlap is essential at this order.

| Possible loss | Fraction of all partitions |
| --- | ---: |
| At least one closed six-point set | At most 72.3% |
| A closed 12- or 18-point set among partitions surviving the first test | Less than 27.7% |

There are at most 54,530 distinct six-point sets that a color can close. The argument pairs disjoint sets and bounds how many partitions also realize a third one. For the larger cuts, the subdivisions on both sides must avoid every smaller closed set. The two losses together leave a winning partition. The general lower bound gives 28. All fractions are exact rational inequalities checked by Lean's ordinary kernel. [Overlap inequality](OverlapCredit.lean) · [Six-point bound](ShortCredit42.lean) · [Larger cuts](LongCredit.lean) · [End-to-end K42 theorem](Exact42.lean)

## K77 and K78

Both orders have wild number 52. The sharper count discards subdivisions that would already have failed a smaller cut test. In a nine-point cut the partner of the temporary root can join any of four matching pairs to make a forbidden triple. Exactly 40 of the 280 subdivisions contain one of these four triples. In a twelve-point cut, divide the six matching pairs into two sets of three. The two sides have ten subdivisions each, excluding at least 100 of 15,400. These deductions suffice in the same rational inequality at K77. The even-order transfer gives K78. [Counting lemmas](InnerCuts.lean) · [Matching argument](TrimmedScopes.lean) · [Final theorem](ExactTrimmed.lean)

## K79 and K80

Both orders have wild number 53. At K79 the fixed group has four vertices. The local count excludes short cuts that lie entirely away from this group. Cuts that contain it enter the final sum as a separate family, even when only one or two other triples lie on their side. This changes the comparison sequence enough to prove existence. [Two-family sieve](SplitLayout.lean) · [Final theorem](ExactSplit.lean)

## K81 and K82

Both orders have wild number 54. Fix one vertex and consider cuts that contain it. Every color that can close a three-point cut uses matching edges that other colors cannot use to close a six-point cut. Bounding the two counts together improves the estimate. Inside a larger closed set, smaller closed sets rule out many subdivisions. Counting individual exclusions and subtracting their pairwise overlaps gives the second improvement. Together the two estimates leave a positive margin at K81. [Joint degree bound](JointDegrees.lean) · [Overlap count](RegionBudget.lean) · [Final theorem](ExactJoint.lean)

## Every order from 155 upward

The same partition count works beyond the finite interval. At an odd order, set aside zero, four or five ordinary vertices, according to the residue modulo three. Write $t$ for the number of free triples and $m=⌊t/2⌋$. A geometric comparison with ratio $1+2/m$ gives two sufficient inequalities. The first controls closed sides consisting of one or two free triples. The second requires the total relative loss from all larger sides to be less than one. [Graph reduction](GraphRule.lean) · [Geometric comparison](GeometricBounds.lean)

For the 526 odd orders from 155 through 1205, Lean checks both inequalities using exact rational arithmetic and its native evaluator. From 1207 upward, $m≥200$. The local counting bounds are at most $10m$ and $31m^3$ for the two short sizes. The larger sizes are bounded by the partition counts for an even number of triples. Their successive ratios control the whole sum uniformly. This part uses ordinary kernel checking. The odd-to-even transfer covers each following even order. [Finite check](GeometricRange.lean) · [Local bounds](GeometricLocal.lean) · [Comparison of larger cuts](GeometricMass.lean) · [Infinite sum bound](GeometricTail.lean) · [End-to-end theorem](ExactLarge.lean)

## Sparse rooted cuts below K77

Complete an odd coloring by adding the missing vertex as a root. Call a triple of ordinary vertices forbidden if some color closes the four-set formed by the triple and the root. The table gives sufficient incidence bounds for the conjectured wild number. Each row applies to every coloring meeting its bound, and to the next even order when the indicated vertex deletion meets it. Count distinct triples, including a triple only once if several colors close its four-set. [Rooted cut degrees](RootTriples.lean) · [Exact graph theorems](SparseOrders.lean)

| Odd order | Maximum forbidden triples through each vertex | Maximum forbidden triples through each pair |
| --- | ---: | ---: |
| 61 | | 1 |
| 65 | 46 | |
| 67 | 45 | 1 |
| 69 | 38 | 1 |
| 71 | 69 | 2 |
| 73 | 70 | 2 |
| 75 | 66 | 2 |

Either column suffices. In a Steiner triple system coloring, any forbidden triple containing a given pair must be its unique Steiner line. This proves the predicted number for every such coloring of K61, K67, K69, K73 and K75. [Steiner graph proof](SteinerOrders.lean)

## Verification

Run `./verification/graph-bounds.sh sieve` from the repository root with Lean 4.19.0. The checker constructs the comparison sequence from integers and tests its inequalities exactly. Lean’s ordinary kernel checks the graph argument and all 44 numerical certificates used in the K77–K154 and even-order proofs. The `large-orders` target replays the proof from 155 upward on its own. The kernel tables are generated during elaboration and every inequality is checked again by kernel reduction. [Kernel certificates](KernelTables.lean) [Arithmetic checker](Numeric.lean) · [Verification guide](../../verification/)
