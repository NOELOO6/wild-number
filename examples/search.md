# Try a coloring

This coloring came from a search that repeatedly changed the colors of lines to make ten-line solutions as scarce as possible. A complete count still found **85,250 successful groupings** of its first fifteen points, out of 1,401,400. This is an example. The minimum over all possible colorings remains unknown. [Coloring data](search-coloring.json) · [Lean count](SearchExample.lean)

| Graph | What was counted | Successful groupings |
| --- | --- | ---: |
| K15 | Five groups of three, after leaving out point 15 | 85,250 |
| K16 | All sixteen choices of the point left untouched | 1,731,000 |
| K16 with point 4 untouched | Five groups of the other fifteen points | 106,880 |
| K16 with point 10 untouched | Five groups of the other fifteen points | 112,355 |

## Run it

From the repository root, use Python 3.10 or later. The first command prints ten actual lines. The second also counts every successful grouping, including a breakdown by untouched point.

```bash
python3 verification/solve.py 15 examples/search-coloring.json
python3 verification/solve.py 16 examples/search-coloring.json --count
```

A grouping counts once. There are three ways to choose two connecting lines inside one group of three, so different line lists can describe the same grouping.

## Enter your own coloring

Supply a JSON object with a `colors` or `mates` array of fifteen rows. Each row can list eight pairs for a color on K16, seven pairs on points 0 through 14 for K15, or the sixteen partner numbers as in the supplied example. For a fifteen-point input the program adds point 15 and pairs it with the point missing from each color. Selecting graph size 15 means deleting that added point. The program validates all fifteen colors before searching.

## Why the search is exhaustive

On K15 a successful set must touch every point, since a color is missing at that point. A two-point wild component also fails for the color of its own line. Thus every wild component has at least three points. Ten edges on fifteen points leave at least five components, forcing exactly five triples. Connecting the three points in a triple takes two wild edges. The solver puts the least unused point into a triple in all possible ways, skipping a cut only when a color already closes it. On K16 every ten-line solution has an untouched point, and deleting that point preserves connectivity in every color. The program tries all sixteen choices if needed. The proved general upper bound of eleven determines the answer if every ten-line grouping fails. [Deletion proof](../cases/k16/) · [Ten-or-eleven bound](../cases/k15/) · [Python solver](../verification/solve.py)
