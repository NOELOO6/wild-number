# Redrawing five colors in any perfect one-factorization of K₁₆

Start with any perfect one-factorization of K₁₆. Select any five colors and repartition the union of their edges into five perfect matchings. For **every** such recoloring and **every** choice of root, ten wild edges avoiding the root connect all fifteen colors. The resulting coloring on K₁₆ and its restriction to the other fifteen vertices both have wild number ten.

With four colors the quantifiers can be strengthened. Fix the factorization, palette and root. There is **one layout** of ten edges that works simultaneously for all proper recolorings of those four colors.

One can also delete the root **before** redrawing the colors. On the fifteen ordinary vertices, allow any proper redraw that retains the other ten color classes, including a change of which vertices miss the redrawn colors. Ten wild edges still suffice. The four-color simultaneous guarantee transfers in the same way. At any odd order, equality of colors outside the chosen palette on ordinary edges forces equality on the new root edges as well. The reason is that a root edge gets color $c$ precisely when its ordinary endpoint misses $c$. [Lean completion equivalence and lifting theorem](PaletteCompletion.lean)

Gill and Wanless classified all 3,155 perfect one-factorizations of K₁₆ up to isomorphism. Their catalogue supplies the starting colorings. The new check covers 68,905,200 rooted four-color palettes and 151,591,440 rooted five-color palettes. Each count is the number of representatives times sixteen roots times the corresponding binomial coefficient on fifteen colors. Distinct rooted palettes can give overlapping sets of recolorings. [Classification paper](https://doi.org/10.1017/S0004972719000856) · [Authors’ catalogue](https://users.monash.edu.au/~iwanless/data/P1F/newP1F.html) · [Local input](../P1F16catalogue)

## Why the check covers every recoloring

Use the root as a singleton and divide the other vertices into five triples. Join each triple by two edges. A matching fails precisely when it closes a pair of blocks. There are five possible sides consisting of the root and a triple, and ten consisting of two ordinary triples. Any disconnected union of blocks has an even number of blocks on each side, since the blocks have odd size and the matching pairs its vertices. One side or its complement therefore has two blocks. For every color the root is a leaf, so deletion preserves connectivity. The usual lower bound gives ten at either order. [Lean cut theorem](../last-two/GraphCuts.lean) · [Leaf deletion](../Delete.lean) · [Graph lower bound](../../../verification/exact/UniversalLower.lean)

Let H be the graph of the selected edges. Some perfect matching of H closes a side S exactly when both S and its complement can be matched internally. For each subset the checker pairs its least vertex with each possible neighbor and consults the result for the smaller subset. It runs these tests for many different palettes at once, keeping a separate bit for each palette. A layout succeeds when none of its fifteen sides is closed by a fixed matching or by any possible matching of H. An initial sample supplies candidate layouts quickly. Any remaining case goes through exhaustive subdivision.

For the five-color cases left over, the checker enumerates the perfect matchings of H. It chooses an uncovered edge at vertex zero. Every full recoloring uses exactly one matching containing that edge. The checker branches over every such matching, adds its closed sides to the fixed list and retains only edge-disjoint matchings for the remaining colors. At each node it searches for a layout that covers every remaining matching. Every actual recoloring follows one of the branches, and a successful leaf supplies its layout. The full check used branching on 368 rooted five-color palettes, visited 2,704 nodes, and fixed at most three matchings along any branch. The colors in the final recoloring need not form a perfect one-factorization.

## Replay

From this directory, compile the standalone C++20 checker and run both sizes. The optional last two arguments are the zero-based first catalogue index and the number of consecutive representatives to verify. The full run uses a single worker. The finite enumeration for the recolorings is in C++. The linked Lean results cover the matching-cut and deletion arguments.

```sh
c++ -std=c++20 -O3 check.cpp -o /tmp/wild-perfect-redraw
/tmp/wild-perfect-redraw ../P1F16catalogue 4
/tmp/wild-perfect-redraw ../P1F16catalogue 5
```
