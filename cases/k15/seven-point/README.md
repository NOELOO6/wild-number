# Can the last K15 grouping be eliminated?

**A winner survives every redraw of the 69 lines touching the chosen six points if the other 36 lines and the missing colors at the nine outside points stay as in the original drawing. The missing colors at the six marked points can change too. In fact, the missing colors at outside points 10 and 14 can also change together.** A winner is a grouping whose ten wild lines connect all fifteen colors. There are 2,800 groupings that keep the six points in two triples and the other nine in three triples. [Proof for the six inside points](OutsideNames.lean) · [Proof allowing two outside points to change as well](SevenOutside.lean)

Each point touches fourteen ordinary lines of different colors, so one of the fifteen colors is missing there. The seven-point rule adds an extra point and uses the missing colors to join it to the fifteen original points. Each color may have at most two lines entirely inside the chosen six points plus the extra point.

| What can change? | What is guaranteed? |
| --- | --- |
| All 54 lines between the six and the nine, with the other lines and the missing colors fixed | At least 19 winners in every one of 854,689 proper redraws. At least two of the original 19 survive. Each bound is attained. [Census](../six-point-trap/CrossCheck.lean) · [Proof](../six-point-trap/CrossResult.lean) |
| All 69 lines touching the six, with the other lines and the nine outside missing colors fixed | At least one winner. [Proof linking the search to paths](RedrawSound.lean) · [Renaming the six points](OutsideNames.lean) |
| All 69 lines and the missing colors, with the original 36 outside lines fixed | At least one winner for 243,144 of the 442,975 outside missing-color lists that pass the basic tests. The counting test covers 243,143 lists, and the original list is a separate case. The count treats the nine outside points as named. [Lists](ExteriorStars.lean) · [Count](ExteriorStarCheck.lean) · [Graph theorem](ExteriorSound.lean) · [Distinct original case](WorkedStar.lean) |
| Any coloring obeying the seven-point rule | Take a split of the six into two triples. If neither triple together with the extra point already cuts off a color, at least 10 of its 280 finishes connect at least 14 colors. [Proof](../six-point-trap/SevenNear.lean) |

The full question remains open. The best strict example here has **15 winners**. It changes some of the 36 outside lines. Seven of its ten initial splits lose every time. The other three give 3, 6 and 6 winners. An earlier example has 16 winners, and the original has 19. Lean followed paths for each win and checked a separating set for each loss. [15-winner coloring](../six-point-trap/sparse-fifteen.txt) · [15-win check](../six-point-trap/FifteenRecord.lean) · [16-win check](../six-point-trap/SparseRecord.lean) · [Original drawing](../vertex-redraw/FixedSix.lean)

## What happens to the original 19?

Changing only the 54 lines between the six and the nine always keeps at least **two of the original winners**. One redraw realizes that limit and has 36 winners in total. [Universal proof](../six-point-trap/KeepTwo.lean) · [Sharp example](../six-point-trap/two-originals-left.txt)

Changing two lines inside the six makes a difference. Exchange colors 1 and 3 on lines **(1, 2)** and **(1, 4)**, and recolor 34 lines between the six and the nine. The outside lines and every missing color keep their original values. All 19 original winners disappear, and **43 different groupings win**. The saved drawing specifies every changed line. [Drawing](../six-point-trap/replace-the-nineteen.txt) · [Lean checks of both examples](../six-point-trap/Replacement.lean)

## Why changing the missing colors matters

Write down the missing color at each of the nine outside points. The nine entries must be distinct. A color already present at an outside point cannot be missing there. Four colors have only one line among the outside nine. Each of those colors must occur on the list, since seven of its outside points need partners among the six marked points and the extra point. These tests give 442,975 lists. The seven-point rule holds throughout this family because a color with three lines among the outside nine has two among the seven. The same endpoint count gives one fewer line on the seven side for every color. [Matching checks](ExteriorEligibility.lean)

For 243,143 lists, Lean checked a specific way to split the outside nine into three triples. That leaves ten ways to split the inside six. Even adding up the failures of all fifteen colors individually, at most nine of those ten possibilities can be spoiled. A winner follows for every proper completion with that list. The cheapest total for the original list is ten, so it adds a different case by the 69-line proof. Together these two proofs cover 243,144 lists, leaving 199,831. The test assumes no particular coloring of the 69 ordinary lines that can change. [Single-color bounds](ExteriorChecks.lean) · [Proof for every completion](ExteriorSound.lean)

There is also a check on the remaining lists. Pick the outside triples supplied for a list and count how many colors fail on each of the ten inside splits. Two colors failing on the same split use up two failures while eliminating just one split. Three colors failing together produce two such repeats.

| Total failures allowed by the checked bound | Number of outside lists | Repeats sufficient for a winner |
| ---: | ---: | ---: |
| 9 or fewer | 243,143 | 0 |
| 10 | 171,870 | 1 |
| 11 | 27,944 | 2 |
| 12 | 18 | 3 |

The counts cover all 442,975 lists. A counterexample would have to stay below the repeat threshold for its supplied outside triples, as well as defeat every other choice of outside triples. The last row counts lists with the loosest supplied bound. All three rows with a positive threshold need further information about the coloring. [Verified counts](ExteriorStarCheck.lean) · [Proof that repeats give a winner](ExteriorSound.lean)

For a small example, change just the missing color at outside point 10 from color 9 to color 2, keeping the missing colors at the other eight outside points. Use the outside triples **(6, 7, 11)**, **(8, 12, 13)** and **(9, 10, 14)**. The fifteen colors together can spoil at most nine of the ten ways to split the six marked points. This works for every proper completion of that prescription. [Concrete coloring](one-outside-change.txt) · [Lean proof](WorkedStar.lean)

## Can the nine outside points be grouped in advance?

**For the original outside missing colors, every redraw has a winner. Yet each of the 280 ways to group the outside nine can be defeated.** Pick any one of them before seeing the 69 redrawn lines. There is a proper redraw that keeps the same 36 outside lines and the same nine outside missing colors, obeys the seven-point rule, and defeats all ten ways to finish that choice. Each example has a winning grouping using different outside triples. [Lean theorem](EndingChoice.lean)

Changing the missing color at exactly one outside point gives 13 lists that pass the matching checks. The other eight outside missing colors and all 36 outside lines stay fixed.

| Outside point | New missing color | What happens if the outside triples are chosen in advance? |
| --- | --- | --- |
| 10 | 2 or 14 | The same choice of outside triples gives a failure bound of nine for both lists. At least one of the ten finishes wins. |
| 9 | 3 or 5 | Every choice can be defeated. |
| 11 | 2, 3, 6, 13 or 14 | Every choice can be defeated. |
| 12 | 2, 3, 6 or 13 | Every choice can be defeated. |

Lean used 207 drawings across the original list and the eleven one-change lists in the last three rows. For each list and each outside grouping, it checked all ten losses on a specific drawing. It also checked a winning grouping on every drawing. A proof for the eleven lists could still choose the outside triples after seeing the redrawn lines. [Witness drawings and their winning groupings](ending-drawings.txt) · [Verification](EndingChoice.lean)

## How Lean checked the 69-line result

The proof assumes every allowed grouping loses. It assigns a value to each variable of a Boolean formula using the actual fifteen color matchings. Lean checks that a clause follows from a single color, from the requirement to color an edge, from two colors being unable to share that edge, or from a grouping losing. The formula has 123,493 clauses. CaDiCaL generated a contradiction, and Lean checked all 5,328,840 steps of the saved run and returned a proof of the graph statement. The six marked points can always be renamed by their missing colors. Lean also checks that this renaming carries winning groupings and their paths back to the original names. Replay generates the large certificate locally. [Finite checks](RedrawChecks.lean) · [Graph argument](RedrawSound.lean) · [Renaming proof](InsideNames.lean) · [Replay entry point](ReplayRedraw.lean)

Run `./verification/replay.sh seven-point` with Lean 4.19.0 and its bundled CaDiCaL. The compressed files contain the formula, the meanings of its variables, the reasons for its clauses, and the data checked for the outside missing colors. The finite proofs use Lean's native evaluator. [Replay script](../../../verification/seven-point.sh)
