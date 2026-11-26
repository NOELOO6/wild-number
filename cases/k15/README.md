# Fifteen points

**Ten wild lines always connect at least fourteen colors.** If a color remains disconnected, it has exactly two pieces. One extra wild line joins them. The open question is whether every coloring already has a choice of ten that connects all fifteen.

| Case or experiment | Conclusion | Evidence |
| --- | --- | --- |
| Every minimum proper coloring | Wild number 10 or 11 | [Written proof](../../reports/k15-wild-number.pdf) and [Lean counting lemma](Near15.lean) |
| Cyclic colorings | Ten suffice for all 631 labeled starting patterns | [Lean](Cyclic15.lean) and [independent path checks](verify_k15.py) |
| Colorings with a rotation of order five | Ten work in both possible cases, including three five-point rings | [Proof and tables](five.md) · [Lean](Five.lean) |
| Colorings with a rotation of order seven | Ten work for all 797,448 compatible pairs of labeled starters | [Proof and explanation](seven.md) · [Lean](Seven.lean) |
| Colorings from two teams of eight | At least 48 of 1,800 tested arrangements work for every admissible initial choice | [Proof, page 2](../../reports/last-color-k15-k16.pdf) and [Lean counts](Teams.lean) |
| Five teams of three | At least 2,592 groupings work, or at least 1,152 if two colors ignore the teams | [Construction and proof](five-teams.md) · [Lean](FiveTeams.lean) |
| Three teams of five | At least 2,400 different groupings work whenever every color pairs within one team and across the other two | [Construction and proof](three-teams.md) · [Lean](ThreeTeams.lean) |
| Two teams with up to two exceptional colors | Ten work even if the two exceptional colors mix within-team and cross-team lines | [Counting proof](trade.md) · [Lean](Trade.lean) |
| Deletions of a perfect one-factorization | Ten suffice for all 3,155 catalogue entries, for every deleted point | [Catalogue verification](../k16/Perfect16.lean) |
| A local test on seven points | A score at most 39 guarantees a completion for every legal coloring of the other 99 lines | [Test and verification](endgame/) |
| A specific seven-point start scoring 40 | Any legal coloring of the other 99 lines admits a completion with ten wild lines | [21-edge table](endgame/#a-score-of-40-that-always-works) · [Lean check](endgame/Completion.lean) |
| The next score can fail | One score-40 start fails all 280 completions. Exchanging points 3 and 4 gives ten successful wild lines. | [Walkthrough](endgame/#a-score-of-40-that-gets-stuck) · [Lean](endgame/Sharp40.lean) |
| Fixing two triples early | A coloring defeats all 280 completions of one choice, then admits a different grouping | [Example](anchor-obstruction.json) |
| Moving a single wild line at a time | One starting arrangement cannot be repaired while keeping fourteen colors connected at every step | [Lean](LineTrap.lean) and [example](line-trap.json) |
| Changing several lines together | One coloring needs four direct replacements from a start that connects fourteen colors | [Walk through the example](../../examples/four-changes.md) · [Lean proof](FourChanges.lean) |
| Swapping points between groups | In another coloring all single swaps miss, but two successive swaps work | [Lean](HardRepair.lean) and [example](two-swaps.json) |

A failed starting arrangement shows what that repair method can miss. To disprove the ten-line conjecture, a coloring must defeat **every** starting arrangement. [Independent example check](check_example.py) · [Verification instructions](../../verification/)
