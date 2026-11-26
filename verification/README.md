# Check a result

Use Lean **4.19.0**, Python **3.10 or later**, Bash and gzip. The Lean sources use its standard library. Run from the repository root.

| What to check | Command |
| --- | --- |
| The 13-point obstruction certificate and its regenerated formula | `./verification/replay.sh k13` |
| The 15-point counts, examples and Python cross-checks | `./verification/replay.sh k15` |
| The 16-point deletion theorem and catalogue witnesses | `./verification/replay.sh k16` |
| All of the above | `./verification/replay.sh` |
| Just the two-line repair example, using Python | `python3 cases/k15/check_example.py` |

To use a separate Lean installation, set `LEAN` to its executable. The script creates compiled modules and uncompressed proof data in a temporary directory.

The ordinary Lean kernel checks the cyclic starter proof and the sixteen-point deletion argument. Several larger finite enumerations use `native_decide`, which also trusts Lean’s native evaluator. The source files print the axioms of their main results. The 13-point LRAT proof checks the specified formula. Its relationship to the graph problem is established in the written report.

For independent 13-point checks, run `python3 cases/k13/verify_k13.py` or compile and run [the C++ enumerator](../cases/k13/crosscheck_k13.cpp). The 16-point catalogue generator has its own independent connectivity test. [Case pages](../README.md#results-by-graph-size)
