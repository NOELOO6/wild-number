# Bisections and quartet redraws on K16

Every proper fifteen-color drawing admits a division into two sets of eight in which every color crosses the division. At most two colors have three matching edges inside either half. Each remaining color has at most two. The two halves have the same internal count for a given color. The proof counts choices of three matching edges inside an eight-point set and averages over all such sets. [Lean theorem](HalfMoment.lean)

## A quartet redraw that always fails

Use the four consecutive groups 0–3, 4–7, 8–11 and 12–15 in the supplied coloring. Within each group, all six ordinary edges have different colors. Connecting each group with wild edges connects every color on the full graph. Pick one point from each group, form a new triple from three of the picked points and leave the fourth alone. This leaves five triples and one singleton. All 1,024 choices disconnect at least one color. Lean checks a cut for every choice, even if additional wild edges are allowed inside the resulting groups. [Coloring](coloring.json) · [Cut certificates and ten-line solution](QuartetTrap.lean)

The same coloring admits ten wild lines. One solution uses the paths 0–1–2, 3–4–5, 6–7–9, 8–10–14 and 11–12–13. Across every choice of five triples and a singleton, 1,942,193 of the 22,422,400 groupings succeed. With point 15 fixed as the singleton, 126,044 of 1,401,400 succeed. Lean and the independent Python solver give the same counts. [Counts by singleton](QuartetCount.lean) · [Graph cut criterion](../last-two/GraphCuts.lean)

Run `./verification/graph-bounds.sh sieve` for the universal bisection theorem and `./verification/graph-bounds.sh regrouping` for the coloring, cuts and enumeration. Replay the independent count with `python3 verification/solve.py 16 cases/k16/quartets/coloring.json --count`.
