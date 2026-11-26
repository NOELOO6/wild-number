# Keep the first triple and clear another split

**For every coloring, every eligible starting triple has at least 1,824 completions that clear all the cuts involving it and all single-group cuts. At least twelve different ways of dividing the other twelve points into two halves also clear the split between those halves.** Choosing one of those twelve divisions leaves only **two** possible splits that can still go wrong.

Here an eligible starting triple is one that no color cuts off by itself. This works on fifteen points and on sixteen after any choice of root.

There is another way to use the number 1,824. A prescribed split into halves occurs in only 100 of the completions. You can therefore forbid **any eighteen** particular splits in advance and at least 24 completions remain. In particular, four specified colors of type Z can be kept connected, or one color of type X or Y and two of type Z. The three color types are described in the [first-triple proof](first-triple.md).

## Count both halves together

Use the forbidden triples on the remaining twelve points from the [first-triple proof](first-triple.md). Write $m$ for their number after removing repetitions. For a six-point side $S$, let $a$ be the number of forbidden triples in it and $p$ the number of complementary pairs of forbidden triples in it. It has exactly $c=10-a+p$ ways to split into two allowed triples. On its opposite side use $b,q,d$ for the corresponding quantities.

There are 462 unordered splits into two halves. Call a split usable if both $c$ and $d$ are positive. It gives $cd$ completions. Each completion occurs for exactly three splits, so three times the number of completions is the sum of $cd$. The number of usable splits is the sum of the indicators of $cd>0$.

A type X or Y color has five pairs inside the twelve points. It can cause at most ten of the 462 splits to fail, one for each choice of three of those pairs. A type Z color has four pairs and can spoil at most four splits. There are six X or Y colors and nine Z colors. Thus at most 96 different splits can fail. The count below gives at least 108 usable splits, leaving at least twelve that also pass this test.

## Four sums that can be checked without knowing the coloring

Let $L=\sum_v\binom{d_v}{2}$ for the degrees of the distinct forbidden triples, and let $P$ be the number of their disjoint pairs. Summing over all halves gives

$$\sum(a+b)=84m,\qquad \sum(p+q)=P,\qquad \sum ab=20P.$$

A given forbidden triple belongs to 84 six-point sets. Each pair of disjoint triples makes one six-point set and lies on opposite sides in twenty distinct splits.

The fourth identity is

$$\sum\left[\binom a2+\binom b2-15(p+q)\right]=21L-14\binom m2.$$

To verify it, two triples that have zero, one or two points in common occur together on a six-point side in one, seven or twenty-eight ways respectively. Subtract fifteen if they are disjoint. The resulting weights are $-14,7,28$, which equal $21$ times the intersection size minus $14$ in every case.

## How large can the vertex degrees be?

Before removing repetitions the degrees are $18+3k_v$, with $\sum k_v=3$. Put $h=75-m$ and let $l_v$ count deleted occurrences at $v$. Then $\sum l_v=3h$ and $0\le l_v\le h$.

Any pair of points belongs to at most ten forbidden triple occurrences. At most two come from using that pair as an ordinary matching edge. For X and Z together there are at most two more from an endpoint serving as the root's partner. An endpoint that is the other outside partner of an X color contributes at most $k_u+k_v\le3$. In a Z color both points may be partners of points in the initial triple, which can happen at most three times. These cover all the ways listed in the single-color table. At least one occurrence through a pair with deletions remains, so at most nine deleted occurrences use both endpoints.

If $z=\max l_v$, every other loss is at most $\min(z,h+9-z)$ by counting the union of the two sets of deleted occurrences. Hence

$$\sum l_v^2\le z^2+\min(z,h+9-z)(3h-z).$$

The original degrees give $2L\le4068$ before deletions. Expanding $(18+3k_v-l_v)(17+3k_v-l_v)$ gives the stronger upper bound $4068-105h+\sum l_v^2$ after deletions. Also $2L\le51m+243$ by the [earlier degree bound](first-triple.md). Lean uses the smaller upper bound, maximizing the square estimate over the integers $0\le z\le h$.

## Six short inequalities finish the count

Write the local expression

$$A+B(a+b)+C\big[ab-20(p+q)\big]+D\left[\binom a2+\binom b2-15(p+q)\right].$$

In each row the expression is at most the denominator times the indicated reward. There are only ten complementary pairs on either half, so Lean can check every possible $a,p,b,q$ directly.

| Reward | Denominator | $A$ | $B$ | $C$ | $D$ |
| --- | ---: | ---: | ---: | ---: | ---: |
| $cd$ | 746 | 50100 | −2800 | 298 | −545 |
| $cd$ | 84 | 4800 | −230 | 47 | −80 |
| Indicator of $cd>0$ | 819 | 819 | −45 | 2 | −9 |
| Indicator of $cd>0$ | 630 | 630 | −30 | 7 | −10 |
| Indicator of $cd>0$ | 115 | 115 | −7 | 0 | −1 |
| Indicator of $cd>0$ | 98 | 86 | 1 | 6 | −8 |

Summing a row uses just the four identities above. For each $40\le m\le75$, a row for the first reward gives a sum at least 5,470, and a row for the second gives a sum strictly above 107. When $m<40$, each forbidden triple blocks at most 280 of the 15,400 four-group partitions. A half with no usable pairing contains at least ten forbidden triples, giving at most $\lfloor84m/10\rfloor$ unusable splits. These bounds give the same conclusions. Dividing 5,470 by three and rounding up gives **1,824**. [Lean verification of all six inequalities and all numerical bounds](HalfSplits.lean)

The counting identities and their application to color connectivity are written proofs. Lean checks the finite tables and arithmetic. This argument clears one of the three remaining splits in at least twelve distinct ways. Clearing the other two at the same time is still open.
