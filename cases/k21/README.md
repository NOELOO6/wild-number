# Fourteen wild edges for cyclic K21

Every minimum proper coloring of K21 with a 21-cycle permuting its color classes has wild number **14**. The same holds for a minimum proper coloring of K22 if deleting one vertex gives such a coloring. Arbitrary K21 and K22 colorings still have the bounds 14–15. [Exact theorems](Cyclic21.lean) · [Unrestricted bounds](../one-extra/)

Label the ordinary points modulo 21 in cycle order and label each color by its missing point. The color missing at zero pairs the twenty other points. Two of its edges cannot have the same circular length. Translating one to the other would change its missing point while preserving its color. The Lean proof extracts this matching directly from an arbitrary coloring given in cycle coordinates. [Extraction from the coloring](Extract21.lean)

For offsets a and b modulo seven, take the seven triples

```text
{3i, 3(i+a)+1, 3(i+b)+2}     (labels modulo 21).
```

Join the first point of each triple to its two partners. Translation by three preserves these fourteen edges, so paths for the colors missing at 0, 1 and 2 give paths for all 21 colors. Lean tries partners for the least unused point with an unused circular length and checks that one of the 49 layouts passes for every complete matching it reaches. This is a native finite check. The repository’s general lower bound gives equality, and the deletion lemma gives the K22 result. [Search](Starters21.lean) · [Finite certificate](Cyclic21Check.lean) · [Transport of paths](OrbitLayouts.lean)

## A partition theorem for arbitrary colorings

Every minimum proper coloring at odd order 3m, for m ≥ 4, admits a partition into triples such that **every color has an edge leaving each triple**. This includes K15 and K21. A color can still disconnect a union of triples. [Graph theorem](../regrouping/ValidTriples.lean)

A fixed pair has at most three forbidden third vertices. The missing color at either endpoint specifies at most one partner of the other endpoint, and the color of the pair is missing at just one vertex.

More generally, let each pair have at most d forbidden completions in a family of unordered triples. A good partition into m triples exists whenever m > d and m ≥ 2. Choose a partition with the fewest bad rows, including a bad row A and any second row B. If every one-point exchange between A and B fails, each of the nine exchanges identifies two forbidden completions of a cross-pair using a vertex still in A or B. These eighteen incidences are distinct. Across the other m−2 rows there are nine ways per row to transpose it with A and B, using the two independent cyclic shifts. If all these transposes failed, there would be at least 18 + 9(m−2) = 9m incidences across nine pairs, which have capacity 9d. A successful exchange or transpose reduces the number of bad rows. [Unordered triple theorem](../regrouping/SymmetricRepair.lean) · [Ordered variant](../regrouping/TripleRepair.lean)

Run `./verification/graph-bounds.sh cyclic-k21` from the repository root with Lean 4.19.0.
