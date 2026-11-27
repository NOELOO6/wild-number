# Exact wild numbers for K77–K80 and K83–K154

At each of these 76 orders, every minimum proper edge coloring has wild number ⌊4⌈n/2⌉/3⌋. The proof treats the odd orders together. Deleting or adding one vertex transfers the result to the following even order. [Exact theorem](ExactRange.lean) · [Odd/even transfer](../../verification/exact/UniversalLower.lean)

| Orders | Wild number |
| --- | ---: |
| K77, K78 | 52 |
| K79, K80 | 53 |
| K83, K84 | 56 |
| K89, K90 | 60 |
| K91, K92 | 61 |
| K93, K94 | 62 |
| K153, K154 | 102 |

## Counting argument

Add one auxiliary vertex so that every color is a perfect matching. Set aside a small group whose internal edges have distinct colors, then partition the remaining vertices into triples. Within each group, draw a star of wild edges. A color fails to connect precisely when some nonempty proper union of groups has no matching edge crossing its boundary. [Choice of group](Rainbow.lean) · [Graph connectivity](GraphSieve.lean)

The proof first counts partitions avoiding every such cut involving one or two free triples on the smaller side. An inequality for forcing specified triples bounds the cost of excluding each cut. The degrees in this count use the fact that an edge belongs to exactly one color. A final sum bounds the number of surviving partitions lost to larger cuts. At each certified order this sum leaves at least one winning partition. [Partition comparison](TripleCoupling.lean) · [Local edge count](DegreeChord.lean) · [Existence argument](FrozenLayout.lean)

The proof uses the matching and random-partition approach of the separate large-order project. The finite comparison sequence and its order-by-order certificates are developed here. [Large-order proof](https://github.com/1337isnot1337/solved-conjectures/blob/main/results/wild-number-complete-graphs/IMPROVEMENT.md)

## K77 and K78

Both orders have wild number 52. The sharper count discards subdivisions that would already have failed a smaller cut test. In a nine-point cut the partner of the temporary root can join any of four matching pairs to make a forbidden triple. Exactly 40 of the 280 subdivisions contain one of these four triples. In a twelve-point cut, divide the six matching pairs into two sets of three. The two sides have ten subdivisions each, excluding at least 100 of 15,400. These deductions suffice in the same rational inequality at K77. The even-order transfer gives K78. [Counting lemmas](InnerCuts.lean) · [Matching argument](TrimmedScopes.lean) · [Final theorem](ExactTrimmed.lean)

## K79 and K80

Both orders have wild number 53. At K79 the fixed group has four vertices. The local count excludes short cuts that lie entirely away from this group. Cuts that contain it enter the final sum as a separate family, even when only one or two other triples lie on their side. This changes the comparison sequence enough to prove existence. [Two-family sieve](SplitLayout.lean) · [Final theorem](ExactSplit.lean)

## Verification

Run `./verification/graph-bounds.sh sieve` from the repository root with Lean 4.19.0. The checker constructs the comparison sequence from integers and tests its inequalities exactly. Lean’s ordinary kernel checks the graph argument and all 38 numerical certificates. The tables are generated during elaboration and every inequality is checked again by kernel reduction. [Kernel certificates](KernelTables.lean) [Arithmetic checker](Numeric.lean) · [Verification guide](../../verification/)
