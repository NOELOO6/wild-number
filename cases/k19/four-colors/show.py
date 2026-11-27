"""Display the common thirteen wild edges for four colors of the K19 example."""
import argparse
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("colors", type=int, nargs=4, choices=range(19))
    args = parser.parse_args()
    if len(set(args.colors)) != 4:
        parser.error("Choose four different colors.")
    root = Path(__file__).resolve().parent
    key = sum(1 << c for c in args.colors)
    assignments = dict(
        map(int, line.split())
        for line in (root / "palette-layouts.txt").read_text().splitlines()
    )
    labels = (root / "layouts.txt").read_text().splitlines()[assignments[key]]
    groups = [[v for v in range(19) if labels[v] == str(j)] for j in range(6)]
    print("Groups  " + " · ".join("{" + ",".join(map(str, g)) + "}" for g in groups))
    print("Edges   " + " ".join(f"{g[0]}–{v}" for g in groups for v in g[1:]))


if __name__ == "__main__":
    main()
