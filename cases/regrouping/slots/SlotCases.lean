import SlotExamples
import Exchange21Data
import TwoCore19
import TwoCore23

namespace WildSlots.Cases
open WildDeletion WildExact WildCuts.OneExtra Finset Trial

/-- Compute a label for each component from the listed wild and colored edges.
The certificate independently checks paths and constancy on every edge. -/
private def trial {n k : Nat} (g : Coloring n k) (fixed : List (EdgeWalk.Edge n))
    (u v : Three → Fin n) : Trial n k :=
  let vertices := List.finRange n
  let reps := ((List.finRange k).map fun c =>
    let es := fixed ++ CoreTest.colored g c
    (vertices.map fun x =>
      let seen := EdgeWalk.run es n (2^x.val)
      (vertices.find? (fun y => seen.testBit y.val)).getD x).toArray).toArray
  ⟨g,fixed,u,v,fun c x => (reps[c.val]!).getD x.val x⟩

private def roundNine : Coloring 9 9 where
  paint x y := 5*(x+y)
  symm := by decide
  proper := by decide

namespace Rotation21

def t : Trial 21 21 := trial Exchange21.graph
  [(1,2),(1,4),(3,5),(6,7),(9,10),(9,11),(12,13),(12,14),(15,16),(15,17),(19,20)]
  (fun i => (#[0,8,18] : Array (Fin 21))[i.val]!) (fun i => (#[3,6,19] : Array (Fin 21))[i.val]!)

private def masks (c : Fin 21) : Nat := (#[511,511,511,255,511,511,495,255,510,511,511,511,511,511,511,511,511,511,511,511,511] : Array Nat)[c.val]!
private theorem components_ok : t.certified := by native_decide
private theorem every_component_seen : t.reaches := by native_decide
private theorem board : ∀ c i j,t.entry c i j ↔ bits (masks c) i j=true := by native_decide

/-- Exactly the two cyclic orders reconnect all 21 colors. -/
theorem rotations (p : Equiv.Perm Three) :
    Works t.graph (draw t.fixed.toFinset t.point t.dest p) ↔ ∀ i,p i≠i := by
  have choices : ∀ q : Equiv.Perm Three,
      (∀ c i,bits (masks c) i (q i)=true) ↔ ∀ i,q i≠i := by native_decide
  change (∀ c,Connected _) ↔ _
  simp_rw [t.color_iff components_ok every_component_seen masks board p]
  exact choices p

theorem cost : ∀ p : Equiv.Perm Three,
    let w := draw t.fixed.toFinset t.point t.dest p
    w.card=14 ∧ ∀ e∈w,e.1<e.2 := by native_decide

theorem count : ((univ : Finset (Equiv.Perm Three)).filter (fun p => ∀ i,p i≠i)).card=2 := by decide

#print axioms rotations
end Rotation21

namespace Sharp9

def t : Trial 9 9 := trial roundNine
  [(1,2),(4,5),(6,8)]
  (fun i => (#[0,3,7] : Array (Fin 9))[i.val]!) (fun i => (#[1,4,6] : Array (Fin 9))[i.val]!)

private def masks (c : Fin 9) : Nat := (#[509,510,503,511,495,511,511,255,511] : Array Nat)[c.val]!
private theorem components_ok : t.certified := by native_decide
private theorem every_component_seen : t.reaches := by native_decide
private theorem board : ∀ c i j,t.entry c i j ↔ bits (masks c) i j=true := by native_decide

/-- Every three colors can be repaired together. These four cannot. -/
theorem four_needed :
    (∀ S : Finset (Fin 9),S.card≤3 → t.palette S) ∧ ¬t.palette {0,1,2,4} :=
  t.sharp components_ok every_component_seen masks board _ (by decide) (by native_decide) (by native_decide)

#print axioms four_needed
end Sharp9

namespace Sharp19

def t : Trial 19 19 := trial Trap19.graph
  [(1,2),(3,5),(3,6),(7,8),(10,11),(10,12),(13,14),(13,15),(16,17),(16,18)]
  (fun i => (#[0,4,9] : Array (Fin 19))[i.val]!) (fun i => (#[1,3,7] : Array (Fin 19))[i.val]!)

private def masks (c : Fin 19) : Nat := (#[510,511,511,507,511,511,503,511,511,511,511,511,511,479,510,507,511,511,511] : Array Nat)[c.val]!
private theorem components_ok : t.certified := by native_decide
private theorem every_component_seen : t.reaches := by native_decide
private theorem board : ∀ c i j,t.entry c i j ↔ bits (masks c) i j=true := by native_decide

/-- Every three colors can be repaired together. These four cannot. -/
theorem four_needed :
    (∀ S : Finset (Fin 19),S.card≤3 → t.palette S) ∧ ¬t.palette {0,3,6,13} :=
  t.sharp components_ok every_component_seen masks board _ (by decide) (by native_decide) (by native_decide)

#print axioms four_needed
end Sharp19

namespace Sharp21

def t : Trial 21 21 := trial Exchange21.graph
  [(1,2),(4,5),(6,7),(6,8),(9,10),(9,11),(12,13),(12,14),(15,16),(15,17),(19,20)]
  (fun i => (#[3,0,18] : Array (Fin 21))[i.val]!) (fun i => (#[1,4,19] : Array (Fin 21))[i.val]!)

private def masks (c : Fin 21) : Nat := (#[511,495,511,511,511,510,511,511,511,511,503,511,503,511,510,511,511,511,511,509,511] : Array Nat)[c.val]!
private theorem components_ok : t.certified := by native_decide
private theorem every_component_seen : t.reaches := by native_decide
private theorem board : ∀ c i j,t.entry c i j ↔ bits (masks c) i j=true := by native_decide

/-- Every three colors can be repaired together. These four cannot. -/
theorem four_needed :
    (∀ S : Finset (Fin 21),S.card≤3 → t.palette S) ∧ ¬t.palette {1,5,10,19} :=
  t.sharp components_ok every_component_seen masks board _ (by decide) (by native_decide) (by native_decide)

#print axioms four_needed
end Sharp21

namespace Sharp23

def t : Trial 23 23 := trial Trap23.graph
  [(1,2),(3,4),(3,5),(3,6),(8,9),(8,10),(11,12),(11,13),(14,15),(14,16),(17,19),(20,21),(20,22)]
  (fun i => (#[0,7,18] : Array (Fin 23))[i.val]!) (fun i => (#[1,3,17] : Array (Fin 23))[i.val]!)

private def masks (c : Fin 23) : Nat := (#[511,511,511,511,511,511,511,503,511,511,511,511,507,511,511,511,511,511,510,511,511,511,479] : Array Nat)[c.val]!
private theorem components_ok : t.certified := by native_decide
private theorem every_component_seen : t.reaches := by native_decide
private theorem board : ∀ c i j,t.entry c i j ↔ bits (masks c) i j=true := by native_decide

/-- Every three colors can be repaired together. These four cannot. -/
theorem four_needed :
    (∀ S : Finset (Fin 23),S.card≤3 → t.palette S) ∧ ¬t.palette {7,12,18,22} :=
  t.sharp components_ok every_component_seen masks board _ (by decide) (by native_decide) (by native_decide)

#print axioms four_needed
end Sharp23

end WildSlots.Cases
