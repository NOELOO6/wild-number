# Fifteen points

**Ten wild lines always connect at least fourteen colors.** If a color remains disconnected, it has exactly two pieces. One extra wild line joins them. The open question is whether every coloring already has a choice of ten that connects all fifteen.

| Case or experiment | Conclusion | Evidence |
| --- | --- | --- |
| Every minimum proper coloring | Wild number 10 or 11 | [Written proof](../../reports/k15-wild-number.pdf) and [Lean counting lemma](Near15.lean) |
| Cyclic colorings | Ten suffice for all 631 labeled starting patterns | [Lean](Cyclic15.lean) and [independent path checks](verify_k15.py) |
| Colorings with a rotation of order seven | Ten work for all 797,448 compatible pairs of labeled starters | [Proof and explanation](seven.md) · [Lean](Seven.lean) |
| Colorings from two teams of eight | At least 48 of 1,800 tested arrangements work for every admissible initial choice | [Proof, page 2](../../reports/last-color-k15-k16.pdf) and [Lean counts](Teams.lean) |
| Deletions of a perfect one-factorization | Ten suffice for all 3,155 catalogue entries, for every deleted point | [Catalogue verification](../k16/Perfect16.lean) |
| Fixing two triples early | A coloring defeats all 280 completions of one choice, then admits a different grouping | [Example](anchor-obstruction.json) |
| Moving a single wild line at a time | One starting arrangement cannot be repaired while keeping fourteen colors connected at every step | [Lean](LineTrap.lean) and [example](line-trap.json) |
| Changing several lines together | One coloring needs four direct replacements from a start that connects fourteen colors | [Walk through the example](../../examples/four-changes.md) · [Lean proof](FourChanges.lean) |
| Swapping points between groups | In another coloring all single swaps miss, but two successive swaps work | [Lean](HardRepair.lean) and [example](two-swaps.json) |

A failed starting arrangement shows what that repair method can miss. To disprove the ten-line conjecture, a coloring must defeat **every** starting arrangement. [Independent example check](check_example.py) · [Verification instructions](../../verification/)
