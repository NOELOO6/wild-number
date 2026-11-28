# The Wild Number Conjecture for Minimum Proper Edge Colorings of Complete Graphs

Let ρ be an edge coloring of the complete graph K<sub>n</sub>, and let E<sub>c</sub> be the edges of color c. The **wild number** of ρ is the minimum size of a set W of edges such that the spanning graph with edge set E<sub>c</sub> ∪ W is connected for every color c.

Dawkins, Nappo, Tong, and Zimbizi conjecture that every proper edge coloring using the minimum number of colors has the following wild number for n ≥ 3. [Original paper, §6](https://arxiv.org/html/2610.22142v1#S6)

> **wld<sub>ρ</sub>(K<sub>n</sub>) = ⌊4⌈n/2⌉/3⌋**

## Results by graph size

### Results proved in this repository

| Complete graph | Conjectured | Status | Proof or bounds |
| --- | ---: | --- | --- |
| K₁₃, K₁₄ | 9 | ✅ Solved in Lean | [End-to-end theorem](verification/exact/K13K14.lean) · [Proof and credits](cases/k13/) |
| K₁₅, K₁₆ | 10 | Partial | 10–11 · [Two-triple cuts and an exact cycle-type criterion](cases/k15/pair-cuts/) · [All five-color redraws of perfect one-factorizations](cases/k16/perfect-redraw/) · [Exact for Steiner colorings](cases/k15/steiner/) · [K15](cases/k15/) · [K16](cases/k16/) |
| K₁₇, K₁₈ | 12 | ✅ Solved in Lean | [End-to-end theorem](verification/exact/K17K18.lean) · [Counting proof](cases/k17/) |
| K₁₉, K₂₀ | 13 | Partial | 13–14 · [K19 families](cases/k19/) · [General bound](cases/one-extra/) |
| K₂₁, K₂₂ | 14 | Partial | 14–15 · [Graph bounds](cases/one-extra/) · [Exact cyclic cases](cases/k21/) |
| K₂₄ | 16 | Proved by counting | [Proof and exact rational certificate](cases/k24/) · [Lean certificate](cases/k24/CutPrices24.lean) |
| K₃₀ | 20 | ✅ Solved in Lean | [End-to-end theorem](cases/k30/Exact30.lean) · [Counting proof and certificate](cases/k30/) |
| K₃₆ | 24 | ✅ Solved in Lean | [End-to-end theorem and counting proof](cases/k36/) |
| K₆ₘ for every m ≥ 5 | 4m | ✅ Solved in Lean | [Infinite-family theorem](cases/sieve/SixFamily.lean) · [First values](cases/sieve/#orders-divisible-by-six) |
| K₄₇, K₅₃, K₇₃, K₇₄ | 32, 36, 49, 49 | Proved by counting | [Prescribed pair and singleton proofs](cases/absorption/conditioned.md) · [Exact checker](cases/absorption/small_components.py) · [Lean partition identities](cases/absorption/PartitionMoments.lean) |
| K₅₅, K₅₆, K₆₁, K₆₂, K₆₇, K₆₈ | 37, 37, 41, 41, 45, 45 | Proved by counting | [Cuts at a prescribed singleton](cases/absorption/singleton.md) · [Lean endpoint criterion](cases/absorption/AbsorbEdge.lean) |
| K₅₉, K₆₅, K₇₁ | 40, 44, 48 | Proved by counting | [Choosing the last wild edge](cases/absorption/) · [Lean graph repair](cases/absorption/AbsorbEdge.lean) · [Lean counts](cases/absorption/PairAbsorbNumbers.lean) |
| K₆₉, K₇₀ | 46 | Proved by counting | [Longer components and simultaneous six-sets](cases/two-triple-cuts/remaining-regions.md) · [Lean packing theorem](cases/two-triple-cuts/CommonSixes.lean) |
| K₇₅, K₇₆ | 50 | Proved by counting | [Overlapping two-triple cuts](cases/two-triple-cuts/) · [Exact checker](cases/two-triple-cuts/six_sets.py) · [Lean overlap inequality](cases/two-triple-cuts/DisjointSixCredit.lean) |
| Other K₂₃ through K₆₄ | ⌊4⌈n/2⌉/3⌋ | Partial | Conjectured value or one more · [General bound](cases/one-extra/NearRange.lean) · [Cyclic K23 and K24](cases/k23/) · [Cyclic K25 and K26](cases/k25/) · [Cyclic K27 and K28](cases/k27/) · [Sparse rooted cuts below K77](cases/sieve/#sparse-rooted-cuts-below-k77) |
| Every Kₙ with n ≥ 77 | ⌊4⌈n/2⌉/3⌋ | ✅ Solved in Lean | [Uniform theorem](cases/sieve/AllLarge.lean) · [Proof for n ≥ 155](cases/sieve/ExactLarge.lean) |
| K₇₇, K₇₈ | 52 | ✅ Solved in Lean | [End-to-end theorem](cases/sieve/ExactTrimmed.lean) |
| K₇₉, K₈₀ | 53 | ✅ Solved in Lean | [End-to-end theorem](cases/sieve/ExactSplit.lean) |
| K₈₁, K₈₂ | 54 | ✅ Solved in Lean | [End-to-end theorem](cases/sieve/ExactJoint.lean) |
| K₈₃ through K₁₅₄ | ⌊4⌈n/2⌉/3⌋ | ✅ Solved in Lean | [End-to-end theorem](cases/sieve/ExactRange.lean) · [Counting argument](cases/sieve/) |

The conjecture now holds for **every order from K65 onward**. The counts at K65, K67–K71 and K73–K76 use written arguments and finite checkers. K66 and K72 belong to the formalized multiple-of-six family. [Prescribed pair](cases/absorption/) · [Singleton attachment](cases/absorption/singleton.md) · [K69–K70](cases/two-triple-cuts/remaining-regions.md) · [K73–K74](cases/absorption/conditioned.md) · [K75–K76](cases/two-triple-cuts/)

The exact theorems start with an arbitrary minimum proper coloring and prove both bounds. Run `./verification/graph-bounds.sh exact` to replay them. K13–K14, K17–K18 and the 526 odd base orders from 155 to 1205 use Lean’s native evaluator for finite calculations. Lean’s ordinary kernel checks the full K77–K154 interval, every order from 1207 upward, and the infinite family K₆ₘ for m ≥ 6. [Full interval theorem](cases/sieve/ExactInterval.lean) · [Verification guide](verification/)

Combining the original K6 and K12 results, the K18 theorem, the K24 counting proof and the infinite Lean theorem gives **wld(K₆ₘ) = 4m for every minimum proper coloring and every m ≥ 1**. At K24 the count guarantees 33,258,864,925 winning partitions. Lean verifies the finite certificate and several graph inequalities. The remaining counting steps are given in the written proof. [K24 proof and verification](cases/k24/) · [Lean theorem from K30 onward](cases/sieve/SixFamily.lean)

Lean proves that every K30 coloring has at least 2,211,739,995,828,567 winning partitions into ten triples. Its finite checks use the native evaluator. [K30 counting proof and replay](cases/k30/)

At K43–K44 and K49–K50, among other orders, the conjectured edge budget connects every color except possibly one, and that color has exactly two components if disconnected. [Counting proof and verified arithmetic](cases/one-extra/piece-moments/)

Every coloring from K15 through K82 admits a common exterior that leaves six to eight vertices to regroup within the conjectured budget. Whether one split works for every color remains open at the partial orders. [Reduction and checked examples](cases/one-extra/#the-remaining-six-to-eight-vertices)

At each odd order immediately below a solved multiple of six, contracting an incident wild edge of an even optimum leaves at most two pieces per color. One edge repairs every case with at most two distinct cuts. For three cuts, the precise obstruction is a choice of three pairwise disjoint sides. [Reverse-deletion theorem](cases/one-extra/#deleting-a-vertex-from-an-optimal-even-solution)

For a fixed choice of points to rearrange, the repository gives a general bound on how many colors can block every move. The sharp bounds are four colors for three points and thirteen for four. With five chosen points, every proper subset of the palette can work while the full palette fails, even on K15. [Theorems, examples and repairs](cases/regrouping/slots/)

At each remaining order through K76 there are explicit families of minimum colorings for which one layout stays optimal under simultaneous alternating-cycle switches. Examples include 2³² colorings on K19 and 2³⁵⁹ on K75 with fixed vertex labels. [Construction and Lean theorem](cases/regrouping/cycle-families/)

The standard round-robin coloring attains the conjectured value for every order n ≥ 3. [Uniform constructions in Lean](cases/regrouping/CyclicOrders.lean)

### Results from other sources

| Complete graph | Wild number | Status | Source |
| --- | ---: | --- | --- |
| K₃, K₄ | 2 | ✅ Solved | Dawkins et al. |
| K₅, K₆ | 4 | ✅ Solved | Dawkins et al. |
| K₇, K₈ | 5 | ✅ Solved | Dawkins et al. |
| K₉, K₁₀ | 6 | ✅ Solved | Dawkins et al. |
| K₁₁, K₁₂ | 8 | ✅ Solved | Dawkins et al. |
| All n ≥ 155 | ⌊4⌈n/2⌉/3⌋ | Earlier large-order result | @aadrianvv |

Dawkins et al. proved the exact values through K₁₂ and the general lower bound. The partition argument of @aadrianvv established the large-order threshold before the Lean proof here. [Original paper, Theorems 3.4–3.5](https://arxiv.org/html/2610.22142v1#S3.SS3) · [Large-order proof record](https://github.com/1337isnot1337/solved-conjectures/issues/155)

## Verification

The verification guide lists the commands and dependencies for each proof, including checks that use Lean’s native evaluator. [Proof replay](verification/) · [Research reports](reports/) · [K15 coloring solver](examples/search.md)
