# Choosing two points for a swap

Suppose every color except one is connected. The remaining color has exactly two connected pieces. Pick one point in each piece and exchange their places in the wild grouping. This preserves the number of wild edges. For an odd graph, add the usual extra point to complete the matchings, and exchange only ordinary points. [Even graph theorem](GraphSwitch.lean) · [Odd graph theorem](OddSwitch.lean)

## Which swaps repair the failed color?

Let x and y be the chosen points. Remove their two edges of the failed color and leave the wild edges in place. The swap repairs the color if and only if there is still a path between the ends of at least one removed edge. To see this, keep the names on the wild groups and exchange the two points’ color partners instead. The new pair of color edges joins both pieces exactly when that alternative path exists. [Two-component criterion](PartnerSwitch.lean)

There is a lower bound on the number of choices. Suppose one piece contains v points in g wild groups, counting the extra root as its own group if present. At least **v/2 − g + 1** of the matching edges in that piece have the following property. Either endpoint can exchange with any point of the other piece and repair the target color in the augmented graph. For a piece made solely of g ordinary triples this gives at least **g/2 + 1** eligible edges. To prove it, connect the g groups using at most g − 1 matching edges. Every remaining matching edge has an alternative route using that connected subgraph. [Counting proof](DetourCount.lean) · [Endpoint selection theorem](ChoosePoints.lean)

For a previously connected color, write u and v for the partners of x and y. If x and y are partners, their exchange preserves that color. Otherwise remove the edges x–u and y–v. The color stays connected if and only if the remaining graph contains a path from {x, v} to {u, y}. The full test applies this condition to each of the other colors. [Four-endpoint path test](BridgeSwitch.lean) · [Test on actual wild edges](GraphSwitch.lean)

## Three checked drawings

Each starting drawing has one failed color with exactly two pieces. The table counts unordered swaps between ordinary points in different pieces. [Colorings, groupings and Lean checks](SwitchCases.lean)

| Drawing | Failed color | Swaps between pieces | Repair that color | Connect all colors |
| --- | ---: | ---: | ---: | ---: |
| K9, round-robin | 2 | 18 | 18 | 6 |
| K15, supplied coloring | 8 | 36 | 36 | 0 |
| K21, round-robin | 6 | 108 | 102 | 36 |

On K15 the smaller piece consists of points 6, 9 and 10. Each of their 36 exchanges with the other twelve points repairs color 8. Every single exchange between any two points still leaves a disconnected color. For any choice of twelve of the fourteen previously connected colors, one of those 36 exchanges preserves all twelve. Protecting thirteen can already prevent every repair. [Complete partner table](two-piece-k15.txt) · [Protection counts and graph proofs](SwitchCases.lean)

| Stage | Five triples |
| --- | --- |
| Start | {0,1,2} · {3,8,13} · {4,5,11} · {6,9,10} · {7,12,14} |
| Exchange 0 and 4 | {1,2,4} · {3,8,13} · {0,5,11} · {6,9,10} · {7,12,14} |
| Exchange 0 and 6 | {1,2,4} · {3,8,13} · {5,6,11} · {0,9,10} · {7,12,14} |

The first exchange preserves all fourteen previously connected colors. The second connects all fifteen. Joining the points of each final triple in increasing order gives ten legal wild edges. Lean proves the wild number of this coloring is exactly ten. The universal K15 bound remains 10–11. [Exact theorem for the example](SwitchCases.lean)

Run `./verification/graph-bounds.sh regrouping` to replay these results. The general criteria and the selection bound use Lean’s ordinary kernel. The concrete counts and witnesses use the native evaluator.
