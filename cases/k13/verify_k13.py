"""Finite lemma in the K13 wild-number proof. Run with Python 3.10+.

A "blocked" triple is one that the partition cannot use. Test whether a
family satisfying all four bounds in the report can hit every partition of
nine points into three triples. Only integer arithmetic is used.
"""
from itertools import combinations, permutations

def subsets(n, size):
    return [sum(1 << i for i in group) for group in combinations(range(n), size)]

def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit

PAIRS = subsets(8, 2)
TRIPLES = subsets(8, 3)
ROOT = 1 << 8
ALL_EIGHT = ROOT - 1
ALL_TRIPLES = (1 << len(TRIPLES)) - 1

def seven_point_graphs():
    """Keep one graph from each orbit, explicitly marking all its relabelings."""
    edges = subsets(7, 2)
    edge_index = {edge: i for i, edge in enumerate(edges)}
    # A relabeling acts independently on three 7-bit pieces of a graph mask.
    lookups = []
    for perm in permutations(range(7)):
        images = []
        for edge in edges:
            a, b = bits(edge)
            images.append(1 << edge_index[(1 << perm[a]) | (1 << perm[b])])
        tables = []
        for start in (0, 7, 14):
            table = [0] * 128
            for word in range(1, 128):
                index = (word & -word).bit_length() - 1
                table[word] = table[word & (word-1)] | images[start+index]
            tables.append(table)
        lookups.append(tables)

    marked = bytearray(1 << len(edges))
    for graph in range(len(marked)):
        if marked[graph]:
            continue
        a, b, c = graph & 127, (graph >> 7) & 127, graph >> 14
        for first, second, third in lookups:
            marked[first[a] | second[b] | third[c]] = 1
        yield [edges[i] for i in bits(graph)]

def root_links():
    """Delete a maximum-degree point of the eight-point link, then add it back."""
    edge_index = {edge: i for i, edge in enumerate(PAIRS)}
    attachments = [sum(1 << edge_index[(1 << v) | 128] for v in bits(mask))
                   for mask in range(128)]
    for edges in seven_point_graphs():
        base = sum(1 << edge_index[e] for e in edges)
        degrees = [sum(bool(e & (1 << v)) for e in edges) for v in range(7)]
        for neighbors, attachment in enumerate(attachments):
            degree = neighbors.bit_count()
            size = len(edges) + degree
            if 10 <= size <= 23 and all(
                degree >= degrees[v] + ((neighbors >> v) & 1) for v in range(7)
            ):
                yield base | attachment

# If a pair outside the root makes an allowed triple with the root, each of
# the ten splits of the remaining six points gives a two-choice condition.
SPLITS = [[(a, b) for a, b in combinations(range(len(TRIPLES)), 2)
           if not (TRIPLES[a] & TRIPLES[b])
           and (TRIPLES[a] | TRIPLES[b]) == (ALL_EIGHT ^ pair)] for pair in PAIRS]

def all_limits():
    for size, minimum, cap in [(1, 1, None), (4, 2, 30), (7, 3, 33)]:
        for subset in subsets(9, size):
            def qualifies(t):
                return (t & subset).bit_count() >= minimum
            fixed = sum(1 << i for i, e in enumerate(PAIRS) if qualifies(e | ROOT))
            outside = sum(1 << i for i, t in enumerate(TRIPLES) if qualifies(t))
            yield fixed, outside, cap

LIMITS = list(all_limits())

def can_block_every_partition(link):
    degree = link.bit_count()
    budget = 35 - degree
    limits = [((degree if cap is None else cap) - (fixed & link).bit_count(), outside)
              for fixed, outside, cap in LIMITS]
    neighbors = [0] * len(TRIPLES)
    for pair in range(len(PAIRS)):
        if not link & (1 << pair):
            for a, b in SPLITS[pair]:
                neighbors[a] |= 1 << b
                neighbors[b] |= 1 << a

    def search(available, chosen, room):
        # Each unmet condition needs at least one of its two endpoints.
        # Mutually disjoint conditions therefore consume separate triples.
        pool = available
        best_edge = None
        best_score = -1
        lower = 0
        while pool:
            a_bit = pool & -pool
            pool ^= a_bit
            a = a_bit.bit_length() - 1
            partners = pool & neighbors[a]
            if not partners:
                continue
            b_bit = partners & -partners
            pool ^= b_bit
            lower += 1
            if lower > room:
                return False
            b = b_bit.bit_length() - 1
            score = (available & neighbors[a]).bit_count() + (available & neighbors[b]).bit_count()
            if score > best_score:
                best_edge, best_score = (a_bit, b_bit), score

        if best_edge is None:
            return all((chosen & mask).bit_count() <= cap for cap, mask in limits)
        for endpoint in best_edge:
            if search(available ^ endpoint, chosen | endpoint, room - 1):
                return True
        return False

    return search(ALL_TRIPLES, 0, budget)

def main():
    if any(len(rows) != 10 for rows in SPLITS):
        raise RuntimeError("Invalid six-point split table")
    count = 0
    for link in root_links():
        count += 1
        if can_block_every_partition(link):
            raise RuntimeError(f"Counterexample link {link}")
    if count != 26251:
        raise RuntimeError("Unexpected number of links")
    print(f"Eight-point links tested (some are isomorphic): {count}")
    print("Families blocking all 280 partitions within the four bounds: 0")
    print("PASS")

if __name__ == "__main__":
    main()
