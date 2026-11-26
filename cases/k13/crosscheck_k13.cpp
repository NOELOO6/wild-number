// A second, exhaustive check of the nine-point lemma in the report.
// Compile with c++ -std=c++20 -O3 crosscheck_k13.cpp -o crosscheck_k13
// Run ./crosscheck_k13. No input files or external libraries are needed.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <vector>

using Mask = std::uint64_t;
using Graph = std::uint32_t;
constexpr int root = 1 << 8;
constexpr int all_eight = root - 1;
constexpr Mask all_triples = (Mask{1} << 56) - 1;

int size(Mask mask) { return std::popcount(mask); }
Mask bit(int index) { return Mask{1} << index; }

struct Bound {
    Mask outside_triples;
    int remaining;
};

struct NinePointCheck {
    std::array<int, 28> pairs{};
    std::array<int, 56> triples{};
    std::array<int, 256> pair_index{};
    std::array<Mask, 56> adjacent{};
    std::vector<Bound> bounds;

    NinePointCheck() {
        int pair_count = 0, triple_count = 0;
        for (int set = 0; set <= all_eight; ++set) {
            if (size(set) == 2) {
                pair_index[set] = pair_count;
                pairs[pair_count++] = set;
            }
            if (size(set) == 3) triples[triple_count++] = set;
        }
    }

    void add_bound(Graph link, int subset, int minimum, int cap) {
        for (int i = 0; i < 28; ++i) {
            if ((link & bit(i)) && size((pairs[i] | root) & subset) >= minimum) --cap;
        }
        Mask outside = 0;
        for (int i = 0; i < 56; ++i) {
            if (size(triples[i] & subset) >= minimum) outside |= bit(i);
        }
        if (cap < size(outside)) bounds.push_back({outside, cap});
    }

    bool has_cover(Mask left, Mask chosen, int room) const {
        if (room < 0) return false;
        for (auto [mask, cap] : bounds) {
            if (size(chosen & mask) > cap) return false;
        }

        Mask active = 0;
        int pivot = -1, maximum_degree = 0;
        for (Mask s = left; s; s &= s - 1) {
            int i = std::countr_zero(s);
            int degree = size(left & adjacent[i]);
            if (degree > 0) active |= bit(i);
            if (degree > maximum_degree) {
                maximum_degree = degree;
                pivot = i;
            }
        }
        if (pivot < 0) return true;

        // Every pairwise-disjoint edge needs a distinct member of the cover.
        int lower_bound = 0;
        for (Mask pool = active; pool;) {
            int i = std::countr_zero(pool);
            pool &= pool - 1;
            Mask choices = pool & adjacent[i];
            if (choices) {
                pool &= ~bit(std::countr_zero(choices));
                if (++lower_bound > room) return false;
            }
        }

        // A cover either contains the pivot or contains every neighbor of it.
        Mask pivot_bit = bit(pivot);
        Mask neighbors = adjacent[pivot] & active;
        return has_cover(active & ~pivot_bit, chosen | pivot_bit, room - 1) ||
               has_cover(active & ~(pivot_bit | neighbors), chosen | neighbors,
                         room - maximum_degree);
    }

    bool allows_blocker(Graph link) {
        int degree = size(link);
        adjacent.fill(0);
        for (int a = 0; a < 56; ++a) {
            for (int b = 0; b < a; ++b) {
                if (triples[a] & triples[b]) continue;
                int unused_pair = all_eight ^ (triples[a] | triples[b]);
                if (!(link & bit(pair_index[unused_pair]))) {
                    adjacent[a] |= bit(b);
                    adjacent[b] |= bit(a);
                }
            }
        }
        bounds.clear();
        for (int set = 1; set < 511; ++set) {
            switch (size(set)) {
                case 1: add_bound(link, set, 1, degree); break;
                case 4: add_bound(link, set, 2, 30); break;
                case 7: add_bound(link, set, 3, 33); break;
            }
        }
        return has_cover(all_triples, 0, 35 - degree);
    }
};

// Each graph is a 28-bit integer. A permutation acts separately on four
// seven-bit chunks. These tables only accelerate explicit relabeling.
struct Relabeling {
    std::array<std::array<Graph, 128>, 4> chunks{};
    Graph apply(Graph g) const {
        Graph result = 0;
        for (int k = 0; k < 4; ++k) result |= chunks[k][(g >> (7*k)) & 127];
        return result;
    }
};

std::vector<Relabeling> relabelings(const NinePointCheck& check) {
    std::vector<Relabeling> result;
    result.reserve(40320);
    std::array<int, 8> perm{};
    std::iota(perm.begin(), perm.end(), 0);
    do {
        auto& table = result.emplace_back();
        std::array<Graph, 28> images{};
        for (int j = 0; j < 28; ++j) {
            int pair = check.pairs[j], mapped = 0;
            for (int v = 0; v < 8; ++v) {
                if (pair & (1 << v)) mapped |= 1 << perm[v];
            }
            images[j] = Graph{1} << check.pair_index[mapped];
        }
        for (int k = 0; k < 4; ++k) {
            for (unsigned word = 1; word < 128; ++word) {
                table.chunks[k][word] = table.chunks[k][word & (word-1)] |
                                       images[7*k + std::countr_zero(word)];
            }
        }
    } while (std::next_permutation(perm.begin(), perm.end()));
    return result;
}

int main() {
    NinePointCheck check;
    auto permutations = relabelings(check);
    std::vector<Mask> seen(1 << 22);
    int count = 0;
    for (Graph link = 0; link < (Graph{1} << 28); ++link) {
        if (size(link) < 10 || size(link) > 23) continue;
        if (seen[link >> 6] & bit(link & 63)) continue;
        for (const auto& perm : permutations) {
            Graph image = perm.apply(link);
            seen[image >> 6] |= bit(image & 63);
        }
        ++count;
        if (check.allows_blocker(link)) {
            std::cerr << "Counterexample link " << link << '\n';
            return 1;
        }
    }
    if (count != 11488) throw std::runtime_error("Unexpected orbit count");
    std::cout << "Eight-point link orbits: " << count
              << "\nFamilies blocking all 280 partitions within the four bounds: 0\nPASS\n";
}
