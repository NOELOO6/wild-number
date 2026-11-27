# A prescribed pair on K15

In any minimum proper coloring of K15, choose any two vertices. They belong to a triple A for which there is a disjoint triple B with **nine different colors on the nine edges between A and B**. After adjoining the usual sixteenth vertex, all six edges on A together with that vertex also have different colors. [End-to-end K15 theorem](RectangleGraph.lean)

| Step | What the proof establishes |
| --- | --- |
| Choose the third vertex of A | At least ten of the thirteen choices give six different colors on A and the added vertex. |
| Test a candidate A | At each of the twelve remaining vertices, list the three colors of its edges to A. Three disjoint lists give B. If none exist, seven of the lists have a rigid intersection pattern. |
| Vary the third vertex | The two prescribed vertices allow at most two of these seven-vertex obstructions. Together they can exclude at most nine choices for the third vertex, so at least one candidate works. |

Lean checks the intersection counts, the obstruction bound and their application to every K15 coloring in its ordinary kernel. Run `./verification/graph-bounds.sh anchor-packing`. [Counts](ColumnCount.lean) · [Seven-vertex sets](SevenSets.lean) · [Obstruction bound](BarrierRows.lean) · [Selection theorem](RectangleRule.lean)

**Can the two triples always be kept?** A specific start can fail. In the score-40 coloring, all nine crossing edges have distinct colors, both triples pass the six-edge test with the added vertex, and the six edges inside the two triples have distinct colors. All 280 partitions of the remaining nine vertices fail. Another choice of ten wild edges connects every color in the same graph. Lean checks these finite results with its native evaluator. Run `./verification/replay.sh k15`. [Coloring and counts](../endgame/Sharp40.lean) · [Score-40 example](../endgame/#a-score-of-40-that-gets-stuck)

A second coloring tests whether a prescribed pair can always pass the previously proved score-39 criterion. Prescribe vertices 0 and 1. Of the 2,860 starts through them, the lowest eligible score is 40. Ten wild edges still work while keeping 0 and 1 together. The five triples are {0,1,3}, {2,7,13}, {4,5,6}, {8,9,14} and {10,11,12}. Lean checks the coloring, the minimum score, and connectivity in all fifteen colors. [Finite check](PairScore.lean) · [Score definition](../endgame/)
