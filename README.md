# Wild numbers of complete graphs

How many lines in a colored graph need to work as **every** color? On 13 points the answer is **nine**. On 15 points, **ten or eleven** lines suffice. The question is whether ten always work.

[Results by graph size](#results-by-graph-size) · [The last color on 15 points](cases/k15/) · [Replay the proofs](verification/) · [Read the reports](reports/)

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
| 15 | 10 | Every coloring needs 10 or 11. Several families have exact value 10. | [Results and counterexample search](cases/k15/) |
| 16 | 10 | Every coloring needs 10 or 11. Ten work exactly when one vertex deletion works. | [Deletion theorem and catalogue](cases/k16/) |

For other orders the prediction is $\lfloor 4\lceil n/2\rceil/3\rfloor$. An external project reports the conjecture for all orders at least 155. This repository does not independently verify that large-order result. [Public research record](https://github.com/1337isnot1337/solved-conjectures/issues/155)

A seven-point test also certifies some colorings without a symmetry assumption. Its score uses just the 21 lines between the seven points. [Try the test](cases/k15/endgame/)

## Start with an example

On fifteen points, one coloring lets fourteen colors connect while color 6 is stuck. Changing **0–6** and **1–9** to **0–1** and **6–9** together fixes it. Lean checked that every single-line route from the same start must temporarily break one of the fourteen working colors. [Illustrated report](reports/last-color-k15-k16.pdf) · [Coloring and both sets of wild lines](cases/k15/line-trap.json)

A different coloring needs **four** replacements from its starting arrangement. The table shows exactly which lines to erase and draw. [Four-change example](examples/four-changes.md)

## Sources and proof scope

Dawkins, Nappo, Tong and Zimbizi introduced the conjecture in this form and proved the lower bound and cases through 12. The choice of four points and reduction to nine in the 13-point case build on earlier public work. The perfect one-factorization list comes from Gill and Wanless. Each case page identifies what Lean proves and which parts use written arguments or external classifications. These project results are available for independent review. [Original paper](https://arxiv.org/abs/2610.22142) · [Earlier nine-point reduction](https://raw.githubusercontent.com/1337isnot1337/solved-conjectures/main/results/wild-number-complete-graphs/continuation/attempt3/REPORT.md) · [Gill–Wanless catalogue](https://users.monash.edu.au/~iwanless/data/P1F/newP1F.html)
