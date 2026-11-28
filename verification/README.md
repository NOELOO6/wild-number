# Check a result

Use Lean **4.19.0**, Python **3.10 or later**, Bash and gzip. The independent K17 cross-check also uses a C++20 compiler. The accelerated checks build shared modules with the Lean installation’s matching `leanc`. Linux was used for the recorded checks. The rotation and placement sources use its standard library. The separate end-to-end graph bounds use the pinned mathlib release. Run from the repository root.

| What to check | Command |
| --- | --- |
| Unrestricted K30 theorem, guaranteed number of winning partitions and rational certificate | `./verification/graph-bounds.sh k30` and `python3 cases/k30/verify.py` |
| All unrestricted exact orders proved in this repository | `./verification/graph-bounds.sh exact` |
| Exact wild number 9 for every minimum proper coloring of K13 and K14 | `./verification/graph-bounds.sh exact-k13` |
| Exact wild number 12 for every minimum proper coloring of K17 and K18 | `./verification/graph-bounds.sh exact-k17` |
| Exact wild numbers for every multiple of six from 36 upward and every order from K77 upward | `./verification/graph-bounds.sh sieve` |
| All orders from 155 upward, including the uniform large-order proof | `./verification/graph-bounds.sh large-orders` |
| Sparse rooted-cut bounds at seven odd orders and their even transfers | `./verification/graph-bounds.sh sparse-orders` |
| Steiner triple system colorings of K15 and K16 colorings with a Steiner deletion | `./verification/graph-bounds.sh steiner-k15` |
| Unrestricted K36 | `./verification/graph-bounds.sh exact-k36` |
| Cyclic K27 and K28 with a cyclic deletion | `./verification/graph-bounds.sh cyclic-k27` |
| Cyclic K25 and K26 with a cyclic deletion | `./verification/graph-bounds.sh cyclic-k25` |
| Cyclic K23 and K24 with a cyclic deletion | `./verification/graph-bounds.sh cyclic-k23` |
| Cyclic K21, K22 with a cyclic deletion, and the general valid-triple partition | `./verification/graph-bounds.sh cyclic-k21` |
| K15 seven-point rule, partitions of the other nine and a ten-edge sufficient condition | `./verification/graph-bounds.sh exterior` |
| K15 packing test, example coloring and prescribed-pair theorem | `./verification/graph-bounds.sh anchor-packing` |
| Exact K24, K30 and K36 families defined by alternating-cycle counts | `./verification/graph-bounds.sh anchored` |
| One-extra bound, six-to-eight-point reduction for K15 through K82, and K19/K21/K23 obstructions and repairs | `./verification/graph-bounds.sh one-extra` |
| Reassignment rule at every order, closed-form color bound, sharp three- and four-point obstructions, and five-point examples | `./verification/graph-bounds.sh slots` |
| All 1,401,400 groupings of the five-point K15 obstruction | `./verification/graph-bounds.sh slots --count-k15` |
| Round-robin theorem for every order from three upward, common-half selection, single-swap criteria, K9/K15/K21 examples, K16 quartet obstruction and K21 upper bound | `./verification/graph-bounds.sh regrouping` |
| Four exhaustive K15 counts, the redraw of the original 19 and all six-point completions | `./verification/replay.sh six-point-trap` |
| The 13-point obstruction certificate and its regenerated formula | `./verification/replay.sh k13` |
| Three-point and four-point K15 families, the two-swap repair and the 2,800-grouping search | `./verification/replay.sh stars` |
| The seven-point rule, all 69 touching lines, and 243,143 missing-color lists | `./verification/replay.sh seven-point` |
| The 15-point counts, examples and Python cross-checks | `./verification/replay.sh k15` |
| The 16-point deletion theorem and catalogue witnesses | `./verification/replay.sh k16` |
| Every pair of colors in an arbitrary K17 coloring reduces to a certificate representative | `./verification/graph-bounds.sh exact-k17-pairs` |
| The K17/K18 case proof, including independent C++ replay | `./verification/replay.sh k17` |
| The two-color result for K15/K16, examples and moment test | `./verification/replay.sh switches` |
| The unrestricted protected-color theorem and a sufficient test for ten | `./verification/replay.sh protected` |
| The eight-pair K15/K16 family, with any point omitted | `./verification/replay.sh paired` |
| Seventy candidate layouts and the 32-line local pattern | `./verification/replay.sh eight` |
| Every way to redraw six round-robin colors on K15/K16 | `./verification/replay.sh six` |
| The K19 rotation proof, placement counts and repair lemma | `./verification/replay.sh k19` |
| Any eleven or twelve named colors on K15 or thirteen on K16 | `./verification/replay.sh prescribed` |
| Every proper redraw of six colors in the counterexample-search coloring | `./verification/replay.sh search-redraw` |
| Latest K15/K16/K19 last-color counting tables and arithmetic | `./verification/replay.sh last-colors` |
| K16 graph cut criterion and the K19 two-line obstruction and repair | `./verification/graph-bounds.sh last-colors` |
| All standard-library checks above | `./verification/replay.sh` |
| End-to-end graph bounds for arbitrary K15, K16 and K19 colorings | `./verification/graph-bounds.sh` |
| Thirteen lines leaving at most one extra piece in an arbitrary K19 coloring | `./verification/graph-bounds.sh pieces` |
| Thirteen fixed lines for any four-color redraw of the supplied K19/K20 coloring | `./verification/graph-bounds.sh palette19` |
| Thirteen lines after eight round-robin colors on K19 change | `./verification/graph-bounds.sh redraw` |
| Determine the answer for a supplied K15 coloring | `python3 verification/solve.py 15 examples/search-coloring.json` |
| Count all groupings for a supplied K16 coloring | `python3 verification/solve.py 16 examples/search-coloring.json --count` |
| Just the two-line repair example, using Python | `python3 cases/k15/check_example.py` |

To use a separate Lean installation, set `LEAN` to its executable. The script creates compiled modules and uncompressed proof data in a temporary directory.

The ordinary Lean kernel checks every arithmetic inequality for K77 through K154, every order from 1207 upward, the K36 counting proof and the sixteen-point deletion argument. The 526 odd base orders from 155 through 1205 and the cyclic starter scans use native finite checks. Several larger finite enumerations use `native_decide`, which also trusts Lean’s native evaluator. The source files print the axioms of their main results. The standalone K13 LRAT replay checks the original symmetry-reduced formula. The end-to-end K13/K14 replay builds a second formula, proves its meaning in Lean and generates an LRAT proof using the CaDiCaL executable bundled with Lean 4.19.0. It checks all 127,584 clauses and the matching-to-path implications. Allow several gigabytes of temporary disk space in addition to the pinned mathlib cache.

The end-to-end K17/K18 replay reads the checked-in integer prices, verifies all fifteen pair types, and proves that at least 403,637 distinct groupings work for each K17 coloring. It constructs twelve wild edges and proves the matching lower bound for both orders. [Exact theorem](exact/K17K18.lean) · [Counting theorem](exact/GlobalCount.lean) · [Distinct groupings](exact/LayoutIdentity.lean)

For independent 13-point checks, run `python3 cases/k13/verify_k13.py` or compile and run [the C++ enumerator](../cases/k13/crosscheck_k13.cpp). The 16-point catalogue generator has its own independent connectivity test. [Case pages](../README.md#results-by-graph-size)
