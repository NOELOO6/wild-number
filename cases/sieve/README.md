# Exact wild numbers from finite partition counts

At each order from K77 through K154 and every multiple of six from 42 upward, every minimum proper edge coloring has wild number ⌊4⌈n/2⌉/3⌋. The interval proof treats the odd orders together. Deleting or adding one vertex transfers the result to the following even order. [Exact interval theorem](ExactInterval.lean) · [Odd/even transfer](../../verification/exact/UniversalLower.lean)

| Orders | Wild number |
| --- | ---: |
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

## Counting argument

Add one auxiliary vertex so that every color is a perfect matching. Set aside a small group whose internal edges have distinct colors, then partition the remaining vertices into triples. Within each group, draw a star of wild edges. A color fails to connect precisely when some nonempty proper union of groups has no matching edge crossing its boundary. [Choice of group](Rainbow.lean) · [Graph connectivity](GraphSieve.lean)

The proof first counts partitions avoiding every such cut involving one or two free triples on the smaller side. An inequality for forcing specified triples bounds the cost of excluding each cut. The degrees in this count use the fact that an edge belongs to exactly one color. A final sum bounds the number of surviving partitions lost to larger cuts. At each certified order this sum leaves at least one winning partition. [Partition comparison](TripleCoupling.lean) · [Local edge count](DegreeChord.lean) · [Existence argument](FrozenLayout.lean)

The proof uses the matching and random-partition approach of the separate large-order project. The finite comparison sequence and its order-by-order certificates are developed here. [Large-order proof](https://github.com/1337isnot1337/solved-conjectures/blob/main/results/wild-number-complete-graphs/IMPROVEMENT.md)

## Orders divisible by six

At K48, K54, K60, K66 and K72 all vertices can be divided into triples. A color pairs up every vertex. A closed union of triples must therefore contain an even number of triples. The first possible obstruction has six vertices. When a cut divides the vertices equally, its two sides describe the same failure, so the count keeps the side avoiding one fixed point. The resulting inequalities leave a working grouping at all five orders. [Graph proof](EvenTriples.lean) · [Exact values](EvenOrders.lean)

The same construction proves that **K₆ₘ has wild number 4m for every m ≥ 7**, with no upper limit on m. Each of the 2m triples uses two wild edges. To show that at least one partition works, count the fraction of partitions lost to closed sets of each size. At m ≥ 14 their sum is less than one. Lean checks the integer inequalities for 14 ≤ m < 70. For all m ≥ 70 a recurrence bounds the sum by a decreasing sequence, starting with a term of size 5m/(6m−5). The small cases use the K42 overlap count, the stronger local count or the K78 theorem. At orders of 155 and above, this gives an independent Lean proof for one of the classes covered by the external large-order result. [Term recurrence](EvenRatios.lean) · [Uniform estimate](EvenSeries.lean) · [End-to-end theorem](InfiniteEven.lean)

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

## Verification

Run `./verification/graph-bounds.sh sieve` from the repository root with Lean 4.19.0. The checker constructs the comparison sequence from integers and tests its inequalities exactly. Lean’s ordinary kernel checks the graph argument and all 44 numerical certificates. The tables are generated during elaboration and every inequality is checked again by kernel reduction. [Kernel certificates](KernelTables.lean) [Arithmetic checker](Numeric.lean) · [Verification guide](../../verification/)
