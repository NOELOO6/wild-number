# Five teams of three

**Ten wild lines work even if two of the fifteen colors ignore the teams.** A color respects the teams when it pairs two points inside its own team, leaves the third point there unmatched, and pairs up the four other teams in twos. Within each pair of teams the color can match their three points in any order.

| Colors respecting the teams | Guaranteed successful groupings |
| ---: | ---: |
| All fifteen | At least 2,592 |
| At least thirteen | At least 1,152 |

## Move one point from each team

Arrange the five teams in a circle. In every team choose one point to move to the next team clockwise. Each team now has two of its original points and one visitor. Join the three points with two wild lines. The five groups use ten lines altogether.

There are 24 directed circles and $3^5=243$ choices of points to move. These give 5,832 distinct groupings. Each group contains two members of one original team, so its visitor identifies the previous team and the point that moved.

## Count the layouts one color can spoil

Temporarily add a root, joined to the unmatched point of each color. A color disconnects a layout only if it pairs up the root and one entire group, or pairs up two entire groups. Count every such occurrence over the 5,832 layouts. Call the count the color's price. Adding prices gives an upper bound on the total number of failed layouts.

* A color respecting the teams has price **216**. There are fifteen ways to specify which team contains its unmatched point and how the other four teams are paired. This leaves three choices for the unmatched point and six choices for each cross-team matching. Lean checks all $15\times3\times6^2=1{,}620$ possible colors.
* Fifteen such colors spoil at most $15\times216=3{,}240$ layouts. At least 2,592 survive.
* If thirteen respect the teams, the other two together have price at most **1,872**. This leaves at least $5{,}832-13\times216-1{,}872=1{,}152$ layouts. The calculation for these two colors follows below.

## How the two exceptional colors constrain each other

For one color, make a table recording how many points of each team go to each team under the color pairing. Let the unmatched point go to itself. The table is symmetric. For each pair of teams, **nine** points in total go from the first to the second across all fifteen colors, counting multiplicities. This includes the diagonal entries, because each point goes to itself in exactly one color.

A color respecting the teams contributes either zero or three to each table entry. Consequently, the sum of the two exceptional colors' tables is divisible by three in every entry.

The table determines a single color up to renaming points inside each team. The team containing the unmatched point has an odd diagonal entry. Pair its other within-team points, and match the prescribed numbers of points across each pair of teams. Any two ways to do that differ by renaming the points within teams. Those renamings preserve the list of 5,832 layouts and hence the price.

Lean constructs one representative per table. In each team, label the unused points in order of their partners' team numbers. Pair the first unused point with the first available point in the specified team. This generates 1,345 tables. Lean checks every pair whose entries add up to multiples of three and verifies the price bound of 1,872. [Enumeration and counting theorems](FiveTeams.lean)

## Which common team structures are covered?

Think of each color as a rule that sends every point to its partner and leaves its unmatched point fixed. Any point can reach any other by one of these rules. If the rules all preserve a partition into equal-sized teams, the nontrivial team size must divide fifteen. The two possibilities are three teams of five and five teams of three. In each case a color must send its unmatched point's team to itself. It cannot preserve a second team individually, since an odd team cannot be paired internally without another unmatched point. The other teams are paired. The two constructions therefore cover **every** such partition, with no assumption of rotational symmetry. [Three teams of five](three-teams.md)

The same ten lines work on the sixteen-point extension: the root is a leaf in every color. On fifteen points the compulsory root is the extra point. For sixteen points it is enough that one deletion satisfies the team condition. The identification of team structures and the normalization by team labels are written arguments. Lean verifies the layout counts, color prices and the lower bounds on the number of layouts that pass the cut test.
