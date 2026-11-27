import ReassignmentCheck

namespace WildSlots.Quintet
open WildExact WildCuts.OneExtra WildSlots.Certificates Finset

namespace K15

private def table := parseRows (include_str "colorings/quintet-k16.txt")
private def paint := fromRows (n:=15) table
def even : Coloring 16 15 := ⟨paint,by native_decide,by native_decide⟩
def odd := restrict even

def plan {m : Nat} [NeZero m] (g : Coloring m 15) :=
  setup 5 g (r:=15) (by decide) [(5,6),(7,8),(9,10),(11,12),(13,14)]
    #[0,1,2,3,4] #[5,7,9,11,13]

theorem sharp_odd : Sharp (plan odd) 10 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem sharp_even : Sharp (plan even) 10 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem singles_odd : singleChecks (plan odd) := by native_decide
theorem singles_even : singleChecks (plan even) := by native_decide

/-- Moving outside the fixed choice of points connects the whole palette. -/
private def alternative : List (EdgeWalk.Edge 15) :=
  [(5,6),(7,8),(9,10),(0,12),(13,14),(5,11),(1,13),(2,7),(3,9),(0,4)]

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

private def table := parseRows (include_str "colorings/quintet-k18.txt")
private def paint := fromRows (n:=17) table
def even : Coloring 18 17 := ⟨paint,by native_decide,by native_decide⟩
def odd := restrict even

def plan {m : Nat} [NeZero m] (g : Coloring m 17) :=
  setup 5 g (r:=17) (by decide) [(5,6),(7,8),(7,9),(10,11),(12,13),(14,15),(14,16)]
    #[0,1,2,3,4] #[5,7,10,12,14]

theorem sharp_odd : Sharp (plan odd) 12 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem sharp_even : Sharp (plan even) 12 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem singles_odd : singleChecks (plan odd) := by native_decide
theorem singles_even : singleChecks (plan even) := by native_decide

/-- Moving outside the fixed choice of points connects the whole palette. -/
private def alternative : List (EdgeWalk.Edge 17) :=
  [(5,6),(7,8),(7,9),(10,11),(12,13),(14,15),(0,14),(5,16),(1,10),(2,12),(3,14),(4,7)]

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

private def table := parseRows (include_str "colorings/quintet-k20.txt")
private def paint := fromRows (n:=19) table
def even : Coloring 20 19 := ⟨paint,by native_decide,by native_decide⟩
def odd := restrict even

def plan {m : Nat} [NeZero m] (g : Coloring m 19) :=
  setup 5 g (r:=19) (by decide) [(5,6),(7,8),(7,9),(10,11),(12,13),(14,15),(16,17),(16,18)]
    #[0,1,2,3,4] #[5,7,10,12,14]

theorem sharp_odd : Sharp (plan odd) 13 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem sharp_even : Sharp (plan even) 13 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem singles_odd : singleChecks (plan odd) := by native_decide
theorem singles_even : singleChecks (plan even) := by native_decide

/-- Moving outside the fixed choice of points connects the whole palette. -/
private def alternative : List (EdgeWalk.Edge 19) :=
  [(0,6),(7,8),(7,9),(10,11),(12,13),(14,15),(16,17),(16,18),(5,12),(0,1),(2,7),(3,14),(4,10)]

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

private def table := parseRows (include_str "colorings/quintet-k22.txt")
private def paint := fromRows (n:=21) table
def even : Coloring 22 21 := ⟨paint,by native_decide,by native_decide⟩
def odd := restrict even

def plan {m : Nat} [NeZero m] (g : Coloring m 21) :=
  setup 5 g (r:=21) (by decide) [(5,6),(7,8),(9,10),(11,12),(13,14),(15,16),(15,17),(18,19),(18,20)]
    #[0,1,2,3,4] #[5,7,9,11,13]

theorem sharp_odd : Sharp (plan odd) 14 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem sharp_even : Sharp (plan even) 14 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem singles_odd : singleChecks (plan odd) := by native_decide
theorem singles_even : singleChecks (plan even) := by native_decide

/-- Moving outside the fixed choice of points connects the whole palette. -/
private def alternative : List (EdgeWalk.Edge 21) :=
  [(5,6),(7,8),(0,9),(11,12),(13,14),(15,16),(15,17),(18,19),(18,20),(5,10),(1,13),(2,9),(3,11),(4,7)]

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

private def table := parseRows (include_str "colorings/quintet-k24.txt")
private def paint := fromRows (n:=23) table
def even : Coloring 24 23 := ⟨paint,by native_decide,by native_decide⟩
def odd := restrict even

def plan {m : Nat} [NeZero m] (g : Coloring m 23) :=
  setup 5 g (r:=23) (by decide) [(5,6),(7,8),(7,9),(10,11),(12,13),(14,15),(14,16),(17,18),(17,19),(20,21),(20,22)]
    #[0,1,2,3,4] #[5,7,10,12,14]

theorem sharp_odd : Sharp (plan odd) 16 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem sharp_even : Sharp (plan even) 16 :=
  from_checks _ _ (by native_decide) (by native_decide) (by native_decide)

theorem singles_odd : singleChecks (plan odd) := by native_decide
theorem singles_even : singleChecks (plan even) := by native_decide

/-- Moving outside the fixed choice of points connects the whole palette. -/
private def alternative : List (EdgeWalk.Edge 23) :=
  [(0,6),(7,8),(7,9),(10,11),(12,13),(14,15),(14,16),(17,18),(17,19),(20,21),(20,22),(5,12),(1,7),(0,2),(3,14),(4,10)]

theorem exact_odd : Exact odd 16 :=
  CoreTest.winner odd (by decide) alternative (by native_decide) (by native_decide) (by native_decide)

theorem exact_even : Exact even 16 :=
  exact_complete even (by decide) exact_odd

#print axioms sharp_odd
#print axioms sharp_even
#print axioms exact_odd
#print axioms exact_even
end K23

end WildSlots.Quintet
