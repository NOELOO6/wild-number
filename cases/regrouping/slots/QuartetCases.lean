import ReassignmentCheck

namespace WildSlots.Quartet
open WildExact WildCuts.OneExtra WildSlots.Certificates Finset

namespace K13

private def table := parseRows (include_str "colorings/quartet-k14.txt")
private def paint := fromRows (n:=13) table
def even : Coloring 14 13 := ⟨paint,by native_decide,by native_decide⟩
def odd := restrict even

def plan {m : Nat} [NeZero m] (g : Coloring m 13) :=
  setup 4 g (r:=13) (by decide) [(4,5),(6,7),(8,9),(10,11),(10,12)]
    #[0,1,2,3] #[4,6,8,10]

theorem sharp_odd : Sharp (plan odd) 9 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem sharp_even : Sharp (plan even) 9 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

/-- Moving outside the fixed choice of points connects the whole palette. -/
private def alternative : List (EdgeWalk.Edge 13) :=
  [(4,5),(6,7),(0,9),(10,11),(10,12),(4,8),(1,6),(0,2),(3,10)]

theorem exact_odd : Exact odd 9 :=
  CoreTest.winner odd (by decide) alternative (by native_decide) (by native_decide) (by native_decide)

theorem exact_even : Exact even 9 :=
  exact_complete even (by decide) exact_odd

#print axioms sharp_odd
#print axioms sharp_even
#print axioms exact_odd
#print axioms exact_even
end K13

namespace K15

private def table := parseRows (include_str "colorings/quartet-k16.txt")
private def paint := fromRows (n:=15) table
def even : Coloring 16 15 := ⟨paint,by native_decide,by native_decide⟩
def odd := restrict even

def plan {m : Nat} [NeZero m] (g : Coloring m 15) :=
  setup 4 g (r:=13) (by decide) [(4,5),(6,7),(8,9),(10,11),(12,13),(12,14)]
    #[0,1,2,3] #[4,6,8,10]

theorem sharp_odd : Sharp (plan odd) 10 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem sharp_even : Sharp (plan even) 10 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

/-- Moving outside the fixed choice of points connects the whole palette. -/
private def alternative : List (EdgeWalk.Edge 15) :=
  [(4,5),(6,7),(0,8),(10,11),(12,13),(12,14),(4,9),(1,6),(2,8),(3,10)]

theorem exact_odd : Exact odd 10 :=
  CoreTest.winner odd (by decide) alternative (by native_decide) (by native_decide) (by native_decide)

theorem exact_even : Exact even 10 :=
  exact_complete even (by decide) exact_odd

#print axioms sharp_odd
#print axioms sharp_even
#print axioms exact_odd
#print axioms exact_even
end K15

namespace K17

private def table := parseRows (include_str "colorings/quartet-k18.txt")
private def paint := fromRows (n:=17) table
def even : Coloring 18 17 := ⟨paint,by native_decide,by native_decide⟩
def odd := restrict even

def plan {m : Nat} [NeZero m] (g : Coloring m 17) :=
  setup 4 g (r:=13) (by decide) [(4,5),(6,7),(8,9),(10,11),(10,12),(10,13),(14,15),(14,16)]
    #[0,1,2,3] #[4,6,8,10]

theorem sharp_odd : Sharp (plan odd) 12 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem sharp_even : Sharp (plan even) 12 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

/-- Moving outside the fixed choice of points connects the whole palette. -/
private def alternative : List (EdgeWalk.Edge 17) :=
  [(4,5),(6,7),(0,9),(10,11),(10,12),(10,13),(14,15),(14,16),(4,8),(1,6),(0,2),(3,10)]

theorem exact_odd : Exact odd 12 :=
  CoreTest.winner odd (by decide) alternative (by native_decide) (by native_decide) (by native_decide)

theorem exact_even : Exact even 12 :=
  exact_complete even (by decide) exact_odd

#print axioms sharp_odd
#print axioms sharp_even
#print axioms exact_odd
#print axioms exact_even
end K17

namespace K19

private def table := parseRows (include_str "colorings/quartet-k20.txt")
private def paint := fromRows (n:=19) table
def even : Coloring 20 19 := ⟨paint,by native_decide,by native_decide⟩
def odd := restrict even

def plan {m : Nat} [NeZero m] (g : Coloring m 19) :=
  setup 4 g (r:=13) (by decide) [(4,5),(6,7),(8,9),(10,11),(10,12),(13,14),(13,15),(16,17),(16,18)]
    #[0,1,2,3] #[4,6,8,10]

theorem sharp_odd : Sharp (plan odd) 13 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem sharp_even : Sharp (plan even) 13 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

/-- Moving outside the fixed choice of points connects the whole palette. -/
private def alternative : List (EdgeWalk.Edge 19) :=
  [(4,5),(6,7),(8,9),(10,11),(10,12),(13,14),(13,15),(0,17),(0,18),(4,16),(1,6),(2,8),(3,10)]

theorem exact_odd : Exact odd 13 :=
  CoreTest.winner odd (by decide) alternative (by native_decide) (by native_decide) (by native_decide)

theorem exact_even : Exact even 13 :=
  exact_complete even (by decide) exact_odd

#print axioms sharp_odd
#print axioms sharp_even
#print axioms exact_odd
#print axioms exact_even
end K19

namespace K21

private def table := parseRows (include_str "colorings/quartet-k22.txt")
private def paint := fromRows (n:=21) table
def even : Coloring 22 21 := ⟨paint,by native_decide,by native_decide⟩
def odd := restrict even

def plan {m : Nat} [NeZero m] (g : Coloring m 21) :=
  setup 4 g (r:=13) (by decide) [(4,5),(6,7),(8,9),(10,11),(12,13),(12,14),(15,16),(15,17),(18,19),(18,20)]
    #[0,1,2,3] #[4,6,8,10]

theorem sharp_odd : Sharp (plan odd) 14 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem sharp_even : Sharp (plan even) 14 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

/-- Moving outside the fixed choice of points connects the whole palette. -/
private def alternative : List (EdgeWalk.Edge 21) :=
  [(4,5),(0,7),(8,9),(10,11),(12,13),(12,14),(15,16),(15,17),(18,19),(18,20),(4,6),(0,1),(2,8),(3,10)]

theorem exact_odd : Exact odd 14 :=
  CoreTest.winner odd (by decide) alternative (by native_decide) (by native_decide) (by native_decide)

theorem exact_even : Exact even 14 :=
  exact_complete even (by decide) exact_odd

#print axioms sharp_odd
#print axioms sharp_even
#print axioms exact_odd
#print axioms exact_even
end K21

namespace K23

private def table := parseRows (include_str "colorings/quartet-k24.txt")
private def paint := fromRows (n:=23) table
def even : Coloring 24 23 := ⟨paint,by native_decide,by native_decide⟩
def odd := restrict even

def plan {m : Nat} [NeZero m] (g : Coloring m 23) :=
  setup 4 g (r:=13) (by decide) [(4,5),(6,7),(8,9),(10,11),(10,12),(13,14),(13,15),(16,17),(16,18),(19,20),(19,21),(19,22)]
    #[0,1,2,3] #[4,6,8,10]

theorem sharp_odd : Sharp (plan odd) 16 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem sharp_even : Sharp (plan even) 16 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

/-- Moving outside the fixed choice of points connects the whole palette. -/
private def alternative : List (EdgeWalk.Edge 23) :=
  [(4,5),(0,7),(8,9),(10,11),(10,12),(13,14),(13,15),(16,17),(16,18),(19,20),(19,21),(19,22),(4,6),(0,1),(2,8),(3,10)]

theorem exact_odd : Exact odd 16 :=
  CoreTest.winner odd (by decide) alternative (by native_decide) (by native_decide) (by native_decide)

theorem exact_even : Exact even 16 :=
  exact_complete even (by decide) exact_odd

#print axioms sharp_odd
#print axioms sharp_even
#print axioms exact_odd
#print axioms exact_even
end K23

end WildSlots.Quartet
