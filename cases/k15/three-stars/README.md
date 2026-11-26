# A test using three points of K15

**Ten wild lines connect all fifteen colors whenever three points pass the test below.** Given the missing color at each point, the test needs only the 39 ordinary lines touching those three points. Keeping those missing colors fixed, all 66 lines among the other twelve points can have any colors that complete the proper coloring. The ten wild lines can depend on that completion.

## How to check a drawing

In a minimum proper coloring of K15, exactly one color is missing at each point. Call an extra point the root. Join it to each old point in its missing color. Each color now pairs up all sixteen points.

1. Choose three old points, A, B and C. The line AB must have the color missing at C, the line AC the color missing at B, and the line BC the color missing at A.
2. For each of the other twelve colors, start at A, B, C and the root and follow one line of that color from each. Write down the four points where you arrive.
3. Check whether the twelve lists give just three distinct sets of four points, with the three sets disjoint. If they do, ten lines suffice.

Once the three sets are identified, each occurs four times. Every point in a set has four lines from the four starting points, and each color using that set uses one of these lines at every point.

## Why seven cases cover the test

Within a set of four outside points, name the four colors by their partners at the root. Each of A, B and C then gives a permutation of the same four names. The four partner lists, including the root's list, have a different name at every position. There are 24 possible tables with this labeling. After renaming the four outside points and their four colors together, a table has one of four types.

In type V, all three permutations consist of two exchanges. In each other type, one of A, B and C has two exchanges, and the other two give a cycle of length four. In the table below, the letter indicates which starting point has two exchanges. Renaming A, B and C and reordering the three outside sets gives seven possibilities. Lean checks the 24 tables, the reduction of all 64 triples of types, and a complete proper coloring realizing each of the seven cases. [Classification checks](StarTypes.lean)

| Types on the three outside sets | Weighted draws checked, including repetitions | Upper bound on the share spoiled |
| --- | ---: | ---: |
| V, V, V | 6,912 | 88.72% |
| V, V, A | 5,888 | 90.06% |
| V, A, A | 4,864 | 93.18% |
| V, A, B | 3,840 | 92.84% |
| A, A, A | 6,912 | 97.93% |
| A, A, B | 2,688 | 96.79% |
| A, B, C | 3,840 | 96.24% |

A draw splits the old points into five groups of three. Two wild lines join the points of each group. The last column counts the total weight that colors could spoil, allowing a draw to be charged several times. Each percentage rounds the verified upper bound **up**. Every entry is below 100%, so every eligible coloring has a surviving draw. The calculation uses integer weights and prices throughout. [Exact data and checks](StarRows.lean)

## What Lean proves

For a given color, a disconnected drawing has a cut. Some three-point group, or the union of two groups, lies entirely on one side of such a cut. The proof forms the set of points reachable from a chosen point, includes the root on the side of its partner, and identifies the cut among the unions of pairs of that color. This turns failure to reach an actual vertex into a charge against the corresponding draw. [Graph proof](StarGeometry.lean) · [Counting proof](CutLedger.lean)

The checker enumerates each individual matching consistent with the three stars. It bounds its charge by a color allowance plus prices for outside edges. When the allowances and prices are added over all fifteen colors, an ordinary edge can be charged only once because its color is unique. The result gives ten distinct edges in the original K15 and a path in every color between every pair of vertices. [Matching and price bounds](StarBounds.lean) · [Final graph theorem](AllStars.lean)

Run `./verification/replay.sh stars` from the repository root. It uses Lean 4.19.0 and its native evaluator. The same ten wild lines also work on the completed K16. For each color, its ordinary line from the restored point joins it to the connected K15. [Lean proof on both graph sizes](RestoreRoot.lean)

The seven coordinate cases and their graph conclusions are checked. The description above explains the choice of names that puts an input drawing into those coordinates.

<details>
<summary>Reading the integer certificates</summary>

Each case has a short text file. For example, V, A, B uses [v01.txt](v01.txt). A row beginning with 0 lists the fifteen color allowances. A row beginning with 1 lists the 66 prices of edges among points 0 through 11, ordered by the larger endpoint and then the smaller one. A row beginning with 2 contains a weight and five triples. Each triple is encoded by adding the powers of two for its points, so 7 represents points 0, 1 and 2. A row beginning with 3 gives a point permutation. Apply every listed permutation to every listed set of five triples to obtain the draws in the table.

</details>
