# The Wild Number Conjecture for Minimum Proper Edge Colorings of Complete Graphs

For an edge coloring $\\rho$ of $K_n$, let $E_c$ be the set of edges of color $c$. The **wild number** $\\operatorname{wld}_\\rho(K_n)$ is the minimum size of a set $W\\subseteq E(K_n)$ such that $(V(K_n),E_c\\cup W)$ is connected for every color $c$.

Dawkins, Nappo, Tong, and Zimbizi conjecture that for every $n\\ge 3$ and every proper edge coloring $\\rho$ using the minimum number of colors,

$$
\\operatorname{wld}_\\rho(K_n)=\\left\\lfloor\\frac{4\\lceil n/2\\rceil}{3}\\right\\rfloor.
$$

They proved the lower bound for every $n$ and equality for $3\\le n\\le12$. [Original paper, §§3.3 and 6](https://arxiv.org/html/2610.22142v1#S3.SS3)

## Results by graph size

| Complete graph | Conjectured | Status | Proof or bounds |
| --- | ---: | --- | --- |
| $K_3$, $K_4$ | 2 | ✅ Solved | [Dawkins et al., Thm. 3.5](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) |
| $K_5$, $K_6$ | 4 | ✅ Solved | [Thm. 3.5](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) |
| $K_7$, $K_8$ | 5 | ✅ Solved | [Thm. 3.5](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) |
| $K_9$, $K_{10}$ | 6 | ✅ Solved | [Thm. 3.5](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) |
| $K_{11}$, $K_{12}$ | 8 | ✅ Solved | [Thm. 3.5](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) |
| $K_{13}$, $K_{14}$ | 9 | ✅ Solved | [Computer-assisted proof](cases/k13/) |
| $K_{15}$, $K_{16}$ | 10 | Partial | 10–11 · [K15](cases/k15/) · [K16](cases/k16/) |
| $K_{17}$, $K_{18}$ | 12 | ✅ Solved | [Counting proof](cases/k17/) |
| $K_{19}$ | 13 | Partial | 13–14 · [Bounds and solved families](cases/k19/) |
| $K_n$, $n\\ge155$ | As above | Reported solved | [External proof and verification record](https://github.com/1337isnot1337/solved-conjectures/issues/155) |

## Verification

The case directories document the proofs and their dependencies. For $K_{13}$, the graph reduction is a written proof and Lean checks the resulting finite certificate. The verification guide gives the commands for replaying each result and identifies checks that use Lean’s native evaluator. [Proof replay](verification/) · [Research reports](reports/) · [K15 coloring solver](examples/search.md)
