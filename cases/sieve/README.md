# Exact wild numbers from K83 through K154

For each of the 72 orders in this interval, every minimum proper edge coloring has wild number ⌊4⌈n/2⌉/3⌋. The proof treats the odd orders together. Deleting or adding one vertex transfers the result to the following even order. [Exact theorem](ExactRange.lean) · [Odd/even transfer](../../verification/exact/UniversalLower.lean)

| Orders | Wild number |
| --- | ---: |
| K83, K84 | 56 |
| K89, K90 | 60 |
| K91, K92 | 61 |
| K93, K94 | 62 |
| K153, K154 | 102 |

## Counting argument

Add one auxiliary vertex so that every color is a perfect matching. Set aside a small group whose internal edges have distinct colors, then partition the remaining vertices into triples. Within each group, draw a star of wild edges. A color fails to connect precisely when some nonempty proper union of groups has no matching edge crossing its boundary. [Choice of group](Rainbow.lean) · [Graph connectivity](GraphSieve.lean)

The proof first counts partitions avoiding every such cut involving one or two free triples on the smaller side. An inequality for forcing specified triples bounds the cost of excluding each cut. The degrees in this count use the fact that an edge belongs to exactly one color. A final sum bounds the number of surviving partitions lost to larger cuts. At each certified order this sum leaves at least one winning partition. [Partition comparison](TripleCoupling.lean) · [Local edge count](DegreeChord.lean) · [Existence argument](FrozenLayout.lean)

The proof uses the matching and random-partition approach of the separate large-order project. The finite comparison sequence and its order-by-order certificates are developed here. [Large-order proof](https://github.com/1337isnot1337/solved-conjectures/blob/main/results/wild-number-complete-graphs/IMPROVEMENT.md)

## Verification

Run `./verification/graph-bounds.sh sieve` from the repository root with Lean 4.19.0. The checker constructs the comparison sequence from integers and tests its inequalities exactly. Lean’s ordinary kernel checks the graph argument and all 36 numerical certificates. The tables are generated during elaboration and every inequality is checked again by kernel reduction. [Kernel certificates](KernelTables.lean) [Arithmetic checker](Numeric.lean) · [Verification guide](../../verification/)
