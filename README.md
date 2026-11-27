# The Wild Number Conjecture for Minimum Proper Edge Colorings of Complete Graphs

Let ρ be an edge coloring of the complete graph K<sub>n</sub>, and let E<sub>c</sub> be the edges of color c. The **wild number** of ρ is the minimum size of a set W of edges such that the spanning graph with edge set E<sub>c</sub> ∪ W is connected for every color c.

Dawkins, Nappo, Tong, and Zimbizi conjecture that every proper edge coloring using the minimum number of colors has the following wild number for n ≥ 3. [Original paper, §6](https://arxiv.org/html/2610.22142v1#S6)

> **wld<sub>ρ</sub>(K<sub>n</sub>) = ⌊4⌈n/2⌉/3⌋**

## Results by graph size

### Results proved in this repository

| Complete graph | Conjectured | Status | Proof or bounds |
| --- | ---: | --- | --- |
| K₁₃, K₁₄ | 9 | ✅ Solved in Lean | [End-to-end theorem](verification/exact/K13K14.lean) · [Proof and credits](cases/k13/) |
| K₁₅, K₁₆ | 10 | Partial | 10–11 · [K15](cases/k15/) · [K16](cases/k16/) |
| K₁₇, K₁₈ | 12 | ✅ Solved in Lean | [End-to-end theorem](verification/exact/K17K18.lean) · [Counting proof](cases/k17/) |
| K₁₉, K₂₀ | 13 | Partial | 13–14 · [K19 families](cases/k19/) · [General bound](cases/one-extra/) |
| K₂₁, K₂₂ | 14 | Partial | 14–15 · [Graph bounds](cases/one-extra/) |
| K₂₃ through K₈₂ | ⌊4⌈n/2⌉/3⌋ | Partial | Conjectured value or one more · [End-to-end theorem](cases/one-extra/NearRange.lean) |
| K₈₃ through K₁₅₄ | ⌊4⌈n/2⌉/3⌋ | ✅ Solved in Lean | [End-to-end theorem](cases/sieve/ExactRange.lean) · [Counting argument](cases/sieve/) |

The exact theorems start with an arbitrary minimum proper coloring and prove both bounds. Run `./verification/graph-bounds.sh exact` to replay them. K13–K14 and K17–K18 include native finite checks. Lean’s ordinary kernel checks the full K83–K154 proof, including its arithmetic. [Verification guide](verification/)

The standard round-robin coloring attains the conjectured value for every odd order n ≥ 3. [Uniform constructions in Lean](cases/regrouping/CyclicOrders.lean)

### Results from other sources

| Complete graph | Wild number | Status | Source |
| --- | ---: | --- | --- |
| K₃, K₄ | 2 | ✅ Solved | Dawkins et al. |
| K₅, K₆ | 4 | ✅ Solved | Dawkins et al. |
| K₇, K₈ | 5 | ✅ Solved | Dawkins et al. |
| K₉, K₁₀ | 6 | ✅ Solved | Dawkins et al. |
| K₁₁, K₁₂ | 8 | ✅ Solved | Dawkins et al. |
| All n ≥ 155 | ⌊4⌈n/2⌉/3⌋ | Reported solved | External project |

Dawkins et al. proved the exact values through K₁₂ and the general lower bound. The large-order entry records a result reported by a separate project. [Original paper, Theorems 3.4–3.5](https://arxiv.org/html/2610.22142v1#S3.SS3) · [Large-order proof record](https://github.com/1337isnot1337/solved-conjectures/issues/155)

## Verification

The verification guide lists the commands and dependencies for each proof, including checks that use Lean’s native evaluator. [Proof replay](verification/) · [Research reports](reports/) · [K15 coloring solver](examples/search.md)
