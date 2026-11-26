# Fifteen points

You can name any nine colors that must stay connected. At least 666 groupings connect those nine and at least five of the other six. [New counting proof](nine-named/)

**Ten wild lines always connect at least fourteen colors.** If a color remains disconnected, it has exactly two pieces. One extra wild line joins them. The open question is whether every coloring already has a choice of ten that connects all fifteen.

| Case or experiment | Conclusion | Evidence |
| --- | --- | --- |
| Every minimum proper coloring | Wild number 10 or 11 | [Written proof](../../reports/k15-wild-number.pdf) and [Lean counting lemma](Near15.lean) · [End-to-end eleven-line bound](../../verification/graph-bounds/) |
| Any eleven named colors in any coloring | At least 14,126 ten-line groupings connect all eleven. | [Proof and counts](prescribed/) |
| A pattern of 32 specified lines on the completed graph | Any proper coloring of the other 88 lines leaves at least four successful ten-line choices. | [Concrete table and Lean checks](eight-points/) |
| Redraw any six colors in the difficult search example | Ten connect all fifteen on the original fifteen points, for every proper redraw. | [Checked family](../k16/search-redraw/) |
| Redraw any six colors of a round-robin completion | Ten lines connect all fifteen colors after any specified point is deleted. | [Proof and ten-line example](../k16/recoloring/) |
| Eight pairs in the completed coloring | Exchanging all partners preserves the colors, and the eight pair lines have one color. Every deletion admits ten wild lines. | [Three cases and ticket counts](../k16/paired-colors/) |
| Protect any four colors | Ten lines connect at least fourteen colors including all four. A separate cycle test can guarantee all fifteen. | [General result and quick test](protected-colors/) |
| Rearrange any two colors of a sevenfold-symmetric completion | Every possible deletion still admits ten lines, including asymmetric examples. | [Theorem and example](../k16/two-color-switch/) |
| The K17 counting method on K15 | Even four aggregate failure totals can miss whether any grouping works. | [Exact comparison tables](moment-test/) |
| Five specified colors | Every legal choice of the remaining ten colors admits ten wild lines. | [See the five colors](five-colors/) · [Lean](five-colors/Completion.lean) |
| Cyclic colorings | Ten suffice for all 631 labeled starting patterns | [Lean](Cyclic15.lean) and [independent path checks](verify_k15.py) |
| Colorings with a rotation of order five | Ten work in both possible cases, including three five-point rings | [Proof and tables](five.md) · [Lean](Five.lean) |
| Colorings with a rotation of order seven | Ten work for all 797,448 compatible pairs of labeled starters | [Proof and explanation](seven.md) · [Lean](Seven.lean) |
| Colorings from two teams of eight | At least 48 of 1,800 tested arrangements work for every admissible initial choice | [Proof, page 2](../../reports/last-color-k15-k16.pdf) and [Lean counts](Teams.lean) |
| Five teams of three | At least 2,592 groupings work, or at least 1,152 if two colors ignore the teams | [Construction and proof](five-teams.md) · [Lean](FiveTeams.lean) |
| Three teams of five | At least 2,400 different groupings work whenever every color pairs within one team and across the other two | [Construction and proof](three-teams.md) · [Lean](ThreeTeams.lean) |
| Two teams with up to two exceptional colors | Ten work even if the two exceptional colors mix within-team and cross-team lines | [Counting proof](trade.md) · [Lean](Trade.lean) |
| Two teams with three exceptional colors | Ten lines work after any specified deletion, including every one of the 212,976 genuine case-and-root choices. | [Proof](../k16/three-exceptions/#what-if-the-deleted-point-is-chosen-in-advance) · [Lean](../k16/three-exceptions/EveryDeletion.lean) |
| Deletions of a perfect one-factorization | Ten suffice for all 3,155 catalogue entries, for every deleted point | [Catalogue verification](../k16/Perfect16.lean) |
| Keeping a prescribed first triple | At least 1,824 completions clear the cuts involving that triple. At least twelve ways to split the rest also clear one more cut, leaving two. | [Counting proof](half-splits.md) · [Lean](HalfSplits.lean) |
| Keeping one triple and clearing two of the last three splits | Every eligible first triple has at least four completions with at most one possible bad split. No score cutoff is needed. | [Counting proof](counting/) · [Lean square checks](counting/Squares.lean) |
| Clearing two of the last three splits | A prescribed first triple leaves at most one split to check if at most 63 triples are forbidden, or at most 84 splits are marked. | [Table and proof](two-cuts.md) · [Lean](TwoCuts.lean) |
| A local test on seven points | A score at most 39 guarantees a completion for every legal coloring of the other 99 lines | [Test and verification](endgame/) |
| A specific seven-point start scoring 40 | Any legal coloring of the other 99 lines admits a completion with ten wild lines | [21-edge table](endgame/#a-score-of-40-that-always-works) · [Lean check](endgame/Completion.lean) |
| The next score can fail | One score-40 start fails all 280 completions. Exchanging points 3 and 4 gives ten successful wild lines. | [Walkthrough](endgame/#a-score-of-40-that-gets-stuck) · [Lean](endgame/Sharp40.lean) |
| Fixing two triples early | A coloring defeats all 280 completions of one choice, then admits a different grouping | [Example](anchor-obstruction.json) |
| Moving a single wild line at a time | One starting arrangement cannot be repaired while keeping fourteen colors connected at every step | [Lean](LineTrap.lean) and [example](line-trap.json) |
| Changing several lines together | One coloring needs four direct replacements from a start that connects fourteen colors | [Walk through the example](../../examples/four-changes.md) · [Lean proof](FourChanges.lean) |
| Swapping points between groups | In another coloring all single swaps miss, but two successive swaps work | [Lean](HardRepair.lean) and [example](two-swaps.json) |

A failed starting arrangement shows what that repair method can miss. To disprove the ten-line conjecture, a coloring must defeat **every** starting arrangement. [Independent example check](check_example.py) · [Verification instructions](../../verification/)
