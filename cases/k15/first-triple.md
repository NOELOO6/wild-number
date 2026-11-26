# What can be kept when you choose the first triple?

**Keep any three points that no color cuts off by itself. There are at least 168 ways to group the other twelve points so that no single group gets cut off, and no pair of groups containing your chosen group gets cut off.** This applies to every coloring on fifteen points. On sixteen points it applies after any choice of the root. To get a ten-line solution from one of these arrangements, we still need one where the last three ways to split the four remaining groups in halves are also clear.

A stronger count gives 1,824 completions and guarantees a choice clearing one more split. [Two-half argument](half-splits.md)

There are at least 350 choices for your first triple $T$. Each of the fifteen colors can cut off at most seven of the 455 possible triples.

## The count on twelve points

Add a root $r$ to the fifteen points, as usual, so that every color pairs up all sixteen. Fix an eligible $T$. Among the other twelve points, forbid a triple $U$ if a color pairs up either $r+U$ or $T+U$. A partition of the twelve avoiding these forbidden triples clears all the cuts in the statement.

The six edges among $r$ and $T$ have distinct colors. An equal pair of disjoint edges there would have cut off $T$. This gives the three types below. An outside point is any of the twelve points.

| Type | Number of colors | What lies among the four points | Forbidden outside triples per color |
| --- | ---: | --- | ---: |
| X | 3 | A pair inside $T$ | 10 |
| Y | 3 | A pair from $r$ to $T$ | 0 |
| Z | 9 | No pair | 5 |

For X, two outside points are partnered to the four-point set. Either one, together with any of the five remaining outside pairs, makes a forbidden triple. For Z, the partner of $r$ together with an outside pair makes four forbidden triples. The three partners of the points of $T$ form the fifth.

Let $m$ count distinct forbidden triples, so $m\le75$. At an outside point $v$, their number $d_v$ is at most $18+3k_v$, where the twelve nonnegative integers $k_v$ sum to three. Indeed, an X color contributes degree two except at its two outside partners, where it contributes five. A Z color contributes one except at the partner of $r$, where it contributes four. Each outside point partners $r$ in exactly one color. The three remaining bonuses occur at the partners of the unpaired points of $T$ in the three X colors. [Lean single-color checks](FirstTriple.lean)

## Leave only nine points

For an allowed outside triple $U$, let $b_U$ count the forbidden triples disjoint from $U$. Let $P$ be the number of unordered disjoint pairs of forbidden triples. Each forbidden triple is disjoint from 84 other triples, giving

$$\sum_{U\text{ allowed}} b_U=84m-2P.$$

If $d_{ij}$ counts forbidden triples through both $i$ and $j$, counting how pairs of triples intersect gives

$$2P=m(m-1)-\sum_v d_v(d_v-1)+\sum_{i<j}d_{ij}(d_{ij}-1).$$

The degree bounds give $d_v(d_v-1)\le17d_v+81k_v$. For the 66 point pairs use $d(d-1)\ge6d-12$. Both the vertex degrees and the pair degrees sum to $3m$. Thus $2P\ge m^2-34m-1035$.

A nine-point family of at most 33 forbidden triples can block all partitions only if it contains **all 28 triples through one point**. This follows by filtering the checked nine-point catalogue. Every point here has forbidden degree at most 27. In fact, for each $U$ there are at least $34-b_U$ surviving partitions of the nine points:

* For $b_U\le27$, at least $280-10b_U$ partitions survive, since any one triple hits just ten.
* For $28\le b_U\le33$, pick a point of largest original degree on the remaining nine. Every other point has degree at most 21, since two points cannot both have $k_v\ge2$. Find a surviving partition and add one of its triples avoiding the chosen point to the forbidden set. Repeat while the set has at most 33 triples. The chosen point stays below degree 28. All others stay below 28 as well, since at most five additions are needed before finding the last partition. This yields at least $34-b_U$ distinct survivors.
* For $b_U\ge34$ the lower bound holds automatically.

Each partition of the twelve is counted four times, once for each choice of $U$ among its groups. Writing $N$ for the number of such partitions gives

$$4N\ge34(220-m)-(84m-2P)\ge670.$$

The last inequality holds for every integer $0\le m\le75$, so $N\ge168$. The same count shows at least three distinct choices of $U$ leave at most 29 forbidden triples on the final nine points. [Lean bounds](FirstTriple.lean) · [Nine-point catalogue](endgame/BlockCatalogue.lean)

The double counting and its connection to the graph are written arguments. Lean checks the normalized single-color counts, the finite catalogue filter and the numerical inequalities. A cut between two of the four newly chosen groups and the other two can still obstruct connectivity.
