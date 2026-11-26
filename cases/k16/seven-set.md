# Seven points with at most two lines of each color

**Every coloring on sixteen points has at least 3,040 such sets of seven points.** If one particular point must be included, there are still at least 1,330 choices. This reduces a search on all sixteen points to two smaller sets of seven and nine.

## The count

One color consists of eight disjoint lines. Choosing three of its lines selects six points. There are 56 ways to do this for one color, and 15 colors. Each choice of six points lies inside ten sets of seven points.

| Count | Any seven points | Seven including a specified point |
| --- | ---: | ---: |
| Possible sets | 11,440 | 5,005 |
| Upper bound on sets that contain three whole lines in some color | 8,400 | 3,675 |
| Sets guaranteed to survive | **3,040** | **1,330** |

For the right-hand column, 21 of the 56 choices of three lines of a color include the specified point. Each of those fits in ten sets. The other 35 choices fit in just one set containing that point. This gives 245 exclusions per color. A set can be excluded several times, so subtraction gives a lower bound. [Lean proof](SevenSet.lean)

## What remains to be arranged

Write Z for one surviving seven-point set and R for the other nine points. Choose a point of Z to leave untouched, split the other six into two triples, and split R into three triples. Drawing two wild lines per triple uses ten. There are 70 choices within Z and 280 within R. If the untouched point was fixed in advance, the two numbers are 10 and 280.

Fix the untouched point r and the two triples A and B in Z. The starting choice is usable when each color crosses both four-point sets formed by adjoining r to A or B. The six points in A and B already have a crossing in every color by the choice of Z.

For a triple T in R, test four sets. They are the four points r together with T, the six points of R outside T, and the six points obtained by joining T to A or to B. A triple passes if each of the four sets has a line leaving it in every color. Three disjoint passing triples in R finish the construction. Every possible cut between the five groups has then been checked.

The seven-point count holds for every coloring. It leaves the existence of a successful final split open.
