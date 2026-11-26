# Ten lines with three exceptional colors on sixteen points

**Split the sixteen points into two teams of eight. Ten wild lines suffice if at least twelve of the fifteen colors obey the teams.** A color obeys the teams when all its lines stay within teams or all its lines go across. The other three colors can mix these two kinds of lines freely.

The proof chooses a point to leave untouched. Its choice may depend on the three exceptional colors. This proves the result on sixteen points and on the particular fifteen-point deletion supplied by the proof.

| Finite check | Number |
| --- | ---: |
| Residual graphs after relabeling | 4,983 |
| Ways to split their lines into three unnamed colors | 43,564 |
| Cases already covered by the two-exception theorem | 30,253 |
| Cases checked by choosing an untouched point and a starting triple | 13,311 |

## Why every possibility is in the list

If at most two colors are exceptional, use the [two-exception theorem](../../k15/trade.md). Otherwise, exactly twelve colors obey the split. At most six of them can lie entirely inside teams and at most seven can go entirely across. Using all seven within-team colors or all eight cross-team colors would force every remaining color to obey the split as well. There are two cases.

- **Five within, seven across.** Each point has two unused lines within its team and one unused line across. The cross lines identify the two teams in pairs. The unused lines inside either team form disjoint cycles of lengths 8, 5 and 3, or 4 and 4. Label the first team along these cycles, then apply the same labels to its partners across. Lean generates all 3,507 labeled possibilities for the other team's cycles.
- **Six within, six across.** Each team has an unused perfect matching. The unused cross lines form even cycles and alternate between two perfect matchings. Use one of those to identify the two teams. The other then gives a permutation of eight labels with no fixed point. Its cycle lengths give seven possibilities, from one eight-cycle to four two-cycles. Lean checks all 105 possibilities for each team's own matching.

For each of the ten starting types, the checker permutes the eight labels in every way preserving the fixed cycles or permutation. It checks that every possible input is an image of one of the supplied representatives. For each representative it generates every perfect matching using unused lines. Two disjoint choices determine the third color. Sorting the three matching codes counts each decomposition once.

## Why the twelve unspecified colors cannot spoil every choice

Choose the point to leave untouched and call it 0. Call its team red. Choose a red point $a$ and a blue point $b$. The checker supplies a short list of blue points $c$, each giving a possible starting triple $\{a,b,c\}$. For each such triple, use the 1,800 groupings in the [two-team construction](../../k15/Teams.lean).

Write $u(x,y)=1$ when line $xy$ is available to an ordinary color, and zero when one of the three known colors already uses it. An ordinary color can seal the quartet $\{0,a,b,c\}$ by pairing $0a$ and $bc$, by pairing $0b$ and $ac$, or by pairing $ab$ and $0c$. Each of the lines $0a,0b,ab$ has a unique color, and that color determines at most one $c$. Thus at most $u(0,a)+u(0,b)+u(a,b)$ proposed blue points need to be discarded. The checker always supplies more than this many.

For any remaining $c$, write $t$ for the number of ordinary colors within teams. Adding the single-color costs checked in the two-team proof gives the following bound for the ordinary colors together.

$$96t+120\bigl(u(0,a)+u(b,c)\bigr)+60(12-t)-60\bigl(u(0,b)+u(0,c)\bigr)+240\bigl(u(a,b)+u(a,c)\bigr).$$

For example, an ordinary within-team color costs 96, plus 120 if it uses $0a$ or $bc$. No surviving choice has both in one color. An ordinary cross-team color costs 60, minus 60 if line $0b$ or $0c$ belongs to it, plus 240 if line $ab$ or $ac$ belongs to it. Each available line occurs once across all ordinary colors. The checker adds the three known colors' costs by testing their cuts directly. The total stays strictly below 1,800 for every proposed $c$. At least one grouping therefore works for every color.

Lean checks the orbit coverage, enumerates all decompositions, and checks the stated inequality on every supplied choice. The classification into cycles, the argument for discarding blue points, and the translation to graph connectivity are written above. The exact grouping costs come from the earlier Lean file. [Lean checker](ThreeExceptions.lean) · [Graph representatives](graphs.txt) · [Root and triple choices](choices.txt) · [Replay instructions](../../../verification/)
