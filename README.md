# The Wild Number Conjecture for Minimum Proper Edge Colorings of Complete Graphs

Let ρ be an edge coloring of the complete graph K<sub>n</sub>, and let E<sub>c</sub> be the edges of color c. The **wild number** of ρ is the minimum size of a set W of edges such that the spanning graph with edge set E<sub>c</sub> ∪ W is connected for every color c.

Dawkins, Nappo, Tong, and Zimbizi conjecture that every proper edge coloring using the minimum number of colors has the following wild number for n ≥ 3. [Original paper, §6](https://arxiv.org/html/2610.22142v1#S6)

> **wld<sub>ρ</sub>(K<sub>n</sub>) = ⌊4⌈n/2⌉/3⌋**

## Results by graph size

### Results proved in this repository

| Complete graph | Conjectured | Status | Proof or bounds |
| --- | ---: | --- | --- |
| K₁₃, K₁₄ | 9 | ✅ Solved | [Computer-assisted proof](cases/k13/) |
| K₁₅, K₁₆ | 10 | Partial | 10–11 · [K15](cases/k15/) · [K16](cases/k16/) |
| K₁₇, K₁₈ | 12 | ✅ Solved | [Counting proof](cases/k17/) |
| K₁₉ | 13 | Partial | 13–14 · [Bounds and solved families](cases/k19/) |

The K₁₃ proof builds on an earlier nine-point reduction. The case report credits that work and distinguishes the written graph argument from the finite certificate checked by Lean. [K13 proof and credits](cases/k13/)

### Results from other sources

| Complete graph | Wild number | Status | Source |
| --- | ---: | --- | --- |
| K₃, K₄ | 2 | ✅ Solved | [Dawkins et al., Theorem 3.5](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) |
| K₅, K₆ | 4 | ✅ Solved | [Theorem 3.5](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) |
| K₇, K₈ | 5 | ✅ Solved | [Theorem 3.5](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) |
| K₉, K₁₀ | 6 | ✅ Solved | [Theorem 3.5](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) |
| K₁₁, K₁₂ | 8 | ✅ Solved | [Theorem 3.5](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS3) |
| All n ≥ 155 | ⌊4⌈n/2⌉/3⌋ | Reported solved | [External proof and verification record](https://github.com/1337isnot1337/solved-conjectures/issues/155) |

Dawkins et al. also proved the conjectured expression is a lower bound for every n ≥ 3. [Theorem 3.4](https://arxiv.org/html/2610.22142v1#S3.SS3.SSS1)

## Verification

The verification guide lists the commands and dependencies for each proof, including checks that use Lean’s native evaluator. [Proof replay](verification/) · [Research reports](reports/) · [K15 coloring solver](examples/search.md)
