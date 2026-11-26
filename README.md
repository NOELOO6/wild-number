# Wild numbers of complete graphs

How many lines in a colored graph need to work as **every** color? On 13 and 14 points the answer is **nine**. On 17 and 18 points it is **twelve**. For 15 and 16 points every coloring needs **ten or eleven**, and the question is whether ten always work. On nineteen points every coloring needs thirteen or fourteen, and thirteen suffice for every rotational coloring and after any eight round-robin colors are redrawn.

[Last-color results at a glance](reports/last-two-colors.md) · [Thirteen lines on arbitrary K19](cases/k19/one-piece/) · [Eight colors redrawn on K19](cases/k19/redraw/) · [Choose twelve or thirteen colors](cases/k15/prescribed/) · [End-to-end graph bounds](verification/graph-bounds/) · [Six colors redrawn](cases/k16/recoloring/) · [Nineteen points](cases/k19/) · [Twelve lines on seventeen points](cases/k17/) · [Results by graph size](#results-by-graph-size) · [The last color on 15 points](cases/k15/) · [Replay the proofs](verification/) · [Read the reports](reports/)

## The puzzle

Draw a line between every pair of points. Color the lines using the fewest colors possible, with different colors on lines touching the same point. Choose some lines to be wild. Pick any one color and hide the other colors, keeping the wild lines visible. The goal is to be able to travel between every pair of points, whichever color you pick. The smallest number of wild lines that does this is the **wild number** of that coloring.

The choice of wild lines can depend on the coloring. The conjecture asks for the same minimum **number** for every allowed coloring of a given size.

## Results by graph size

| Points | Predicted wild number | What has been proved | Where to look |
| --- | ---: | --- | --- |
| 3, 4 | 2 | Exact for every minimum proper coloring | [Original paper, §3.3](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) |
| 5, 6 | 4 | Exact for every minimum proper coloring | [Original paper](https://arxiv.org/abs/2610.22142) |
| 7, 8 | 5 | Exact for every minimum proper coloring | [Original paper](https://arxiv.org/abs/2610.22142) |
| 9, 10 | 6 | Exact for every minimum proper coloring | [Original paper](https://arxiv.org/abs/2610.22142) |
| 11, 12 | 8 | Exact for every minimum proper coloring | [Original paper](https://arxiv.org/abs/2610.22142) |
| 13, 14 | 9 | Computer-assisted case proof in this project | [Thirteen-point proof and checks](cases/k13/) |
| 15 | 10 | Ten always connect fourteen colors including any nine you name. The exact value is 10 or 11. | [Results and counterexample search](cases/k15/) |
| 16 | 10 | Ten connect any thirteen named colors and at least one of the other two in 8,527 or more groupings. The exact value is 10 or 11. | [Deletion theorem and catalogue](cases/k16/) |
| 17, 18 | 12 | Exact for every minimum proper coloring. At least 403,637 twelve-line groupings work on K17. | [Proof, table and worked example](cases/k17/) |
| 19 | 13 | Thirteen connect any two named colors and at least sixteen others, leaving at most one extra piece. Thirteen suffice for every rotational coloring and after any eight round-robin colors are redrawn. | [Counts, proof scope and working solver](cases/k19/) |

For other orders the prediction is $\lfloor 4\lceil n/2\rceil/3\rfloor$. An external project reports the conjecture for all orders at least 155. This repository does not independently verify that large-order result. [Public research record](https://github.com/1337isnot1337/solved-conjectures/issues/155)

A 32-line pattern on sixteen points guarantees at least four successful ten-line choices, however the other 88 lines are colored. [See the pattern](cases/k15/eight-points/)

On fifteen and sixteen points, all six colors you name in the standard round-robin coloring may be redrawn together. Ten lines still work, with any specified point untouched. A second ten-line result applies when swapping the members of eight same-color pairs preserves every color. [Six-color theorem](cases/k16/recoloring/) · [Eight-pair theorem](cases/k16/paired-colors/)

On fifteen and sixteen points, a sevenfold coloring can lose its symmetry completely when two colors are rearranged. Ten wild lines still work, with any specified point left untouched on K16. [Proof and concrete example](cases/k16/two-color-switch/)

For every coloring, ten lines can connect fourteen colors including any nine you name on K15 or any thirteen you name on K16. An alternating-cycle test guarantees all fifteen for some colorings. [Nine named on K15](cases/k15/nine-named/) · [Thirteen named on K16](cases/k16/last-two/) · [Full ten-line test](cases/k15/protected-colors/)

On fifteen points, any suitable first triple extends in at least four ways that leave only one split capable of disconnecting a color. [Counting proof](cases/k15/counting/)

On sixteen points, four colors forming a four-dimensional cube guarantee a solution however the other eleven are drawn. A second four-color pattern works too. [Four-color patterns and counts](cases/k16/four-colors/)

A seven-point test also certifies some colorings without a symmetry assumption. Its score uses just the 21 lines between the seven points. [Try the test](cases/k15/endgame/)

## Check a coloring yourself

The repository includes a solver that takes a coloring, finds ten working lines if they exist, and checks the answer by following paths in every color. On the example from the counterexample search, 85,250 groupings work on fifteen points. [Try the solver and see the counts](examples/search.md)

## Start with an example

On fifteen points, one coloring lets fourteen colors connect while color 6 is stuck. Changing **0–6** and **1–9** to **0–1** and **6–9** together fixes it. Lean checked that every single-line route from the same start must temporarily break one of the fourteen working colors. [Illustrated report](reports/last-color-k15-k16.pdf) · [Coloring and both sets of wild lines](cases/k15/line-trap.json)

A different coloring needs **four** replacements from its starting arrangement. The table shows exactly which lines to erase and draw. [Four-change example](examples/four-changes.md)

## Sources and proof scope

Dawkins, Nappo, Tong and Zimbizi introduced the conjecture in this form and proved the lower bound and cases through 12. The choice of four points and reduction to nine in the 13-point case build on earlier public work. The perfect one-factorization list comes from Gill and Wanless. Each case page identifies what Lean proves and which parts use written arguments or external classifications. These project results are available for independent review. [Original paper](https://arxiv.org/abs/2610.22142) · [Earlier nine-point reduction](https://raw.githubusercontent.com/1337isnot1337/solved-conjectures/main/results/wild-number-complete-graphs/continuation/attempt3/REPORT.md) · [Gill–Wanless catalogue](https://users.monash.edu.au/~iwanless/data/P1F/newP1F.html)
