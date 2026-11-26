# Choose which colors must stay connected

Ten wild lines can connect at least fourteen of the fifteen colors in **every** coloring on fifteen or sixteen points. You can also insist in advance that certain colors are among those fourteen.

| Graph | Colors you can name in advance | Additional choice |
| --- | ---: | --- |
| K15 | Any four | The ten wild lines may depend on the coloring and the four names. |
| K16 | Any five | The construction leaves one point untouched. |
| K16 with an untouched point specified in advance | Any four | Delete that point, use the K15 result and put the point back. |

Suppose some coloring really needs eleven lines. Look at all its ten-line choices that connect fourteen colors. On K15 at least **five different colors** must be able to play the part of the one that fails. On K16 there must be at least **six**. Otherwise we could put all the possible failures on our protected list and leave no possible failure at all.

There is also a quick test that proves **all fifteen colors** connect for some colorings. It only looks at the alternating loops made by one color with its fourteen partners. [Jump to the test](#a-test-for-all-fifteen-colors).

## Make the layouts

For K15, temporarily restore the missing-color point. A color now pairs up all sixteen points. Choose a color to protect and label its edges 0–1, 2–3, …, 14–15. The specified point to omit from the wild edges is 0. In the table below, each triple will be connected by two wild lines.

| Layout | Lone point | Five triples |
| --- | ---: | --- |
| A | 0 | {1,2,4}, {3,6,7}, {5,8,10}, {9,12,13}, {11,14,15} |
| B | 0 | {1,2,4}, {3,6,8}, {5,7,10}, {9,12,13}, {11,14,15} |

Both layouts connect the chosen color. On K15 permute the seven pairs other than 0–1 in all possible ways and allow their endpoints to be exchanged independently. This gives $7!2^7=645{,}120$ relabelings. Count each image of A 649 times and each image of B 351 times. On K16 use A alone and allow all eight pairs to move and flip. That gives $8!2^8=10{,}321{,}920$ relabelings. Repeated layouts are intentional. A single surviving draw gives an actual layout.

## Keep two chosen colors connected

Pick a second protected color. Discard draws where it fails. Call the number of remaining draws $L$. For another matching $m$ let $Q(m)$ count how many of these draws it spoils. The two protected colors form disjoint alternating cycles. Their lengths determine the pair up to relabeling. On K15 record the cycle containing point 0 first. On K16 any point may be the singleton, so the lengths can simply be sorted.

For each surviving draw, the six odd blocks disconnect under a matching exactly when two blocks together are closed under that matching. There are fifteen such cuts. If a matching fails, the number of closed two-block cuts is one or three. In the latter case the matching partitions the six blocks into three closed pairs. Count all closed cuts and subtract twice the number of these three-pair decompositions. This gives $Q(m)$ exactly. The checker precomputes, over surviving draws, the frequencies of individual cuts and of three-pair decompositions, then evaluates the formula for every disjoint third matching.

**K15.** For every one of the eleven rooted pair types, every third matching satisfies $15Q(m)<2L$. Thirteen colors remain. Count one penalty when any of them fails, and a second penalty when it is one of the two other protected colors. This gives fifteen contributions. Their total over all draws is less than $2L$. Some draw therefore has at most one penalty. On that draw all four named colors connect, and at most one other color fails.

**K16.** Choose the first two colors among the five protected colors so that their cycles have lengths different from 8 and 8 if there is such a pair. If all ten protected pairs have lengths 8 and 8, choose any two. For each of the seven possible unrooted pair types there is a table of nonnegative integer edge prices $p(e)$ and one extra price $b$. For every disjoint third matching the checker verifies $Q(m)\le\sum_{e\in m}p(e)$. For a third protected color it also verifies $2Q(m)\le\sum_{e\in m}p(e)+b$. When the chosen pair has type (8,8), this second check applies to third colors that form type (8,8) with both chosen colors. Our rule for choosing the first pair guarantees exactly that condition for every remaining protected color.

Across the thirteen remaining colors each unused edge occurs once. There are three extra prices, one for each remaining protected color. The sum of all edge prices plus $3b$ is strictly below $2L$ in each row. Again there is a draw with at most one penalty.

| K16 pair type | Draws surviving the first two colors | Margin below $2L$ |
| --- | ---: | ---: |
| 4, 4, 4, 4 | 9,265,152 | 134,144 |
| 4, 4, 8 | 9,209,856 | 133,624 |
| 4, 6, 6 | 9,303,552 | 242,112 |
| 4, 12 | 9,168,384 | 133,503 |
| 6, 10 | 9,185,280 | 143,766 |
| 8, 8 | 9,134,080 | 23,789 |
| 16 | 9,125,888 | 65,591 |

## A test for all fifteen colors

On the completed sixteen points, choose the point to delete and one reference color. Suppose at least ten of the other fourteen colors have the following property. Their alternating cycles with the reference color have lengths **4, 6 and 6**, and the cycle through the point to delete has length **4**. Then ten wild lines connect **all fifteen colors** on the deletion and the original graph. No symmetry of the coloring is assumed.

To see this, take the 645,120 relabelings of layout A. A partner of the indicated type can spoil 31,104 draws. Any other partner can spoil at most 83,456. Thus at most $10\cdot31{,}104+4\cdot83{,}456=644{,}864$ draws are spoiled. At least 256 survive. These are counts of draws and may include repeated layouts. More generally the check succeeds whenever the fourteen entries from the following table sum to less than 645,120.

| Root cycle | Other cycles | Draws spoiled |
| ---: | --- | ---: |
| 4 | 4, 4, 4 | 66,048 |
| 4 | 4, 8 | 55,552 |
| 8 | 4, 4 | 83,456 |
| 4 | 6, 6 | 31,104 |
| 6 | 4, 6 | 74,496 |
| 4 | 12 | 50,304 |
| 12 | 4 | 79,360 |
| 6 | 10 | 77,440 |
| 10 | 6 | 67,200 |
| 8 | 8 | 74,240 |
| 16 | None | 74,752 |

The supplied example has thirteen partners of type (4,6,6) and one of type (4,12). At least 190,464 draws therefore survive. Lean checks that it is a proper coloring and that these are the actual cycle types. [Example coloring](example.txt) · [Lean example](Example.lean)

Run `./verification/replay.sh protected` from the repository root. Lean verifies the relabeling counts, exact cut counts, all finite matching inequalities, and the averaging argument. The written argument identifies the matching cases and explains why the weights protect the named colors. [Layout counts](Protected.lean) · [Averaging lemma](CheckProtected.lean) · [Two-color counts](TwoAnchors.lean) · [Finite checks](CheckTwo.lean) · [Integer prices](free-prices.txt)
