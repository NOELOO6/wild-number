import QuintetCases

namespace WildSlots.Replacement
open WildExact WildSlots.Certificates

/-- Relabel the wild groups while leaving every ordinary edge at its original color. -/
def exchange {d r n k : Nat} (t : Setup d r n k) (x y : Fin n) : Setup d r n k :=
  let swap := Equiv.swap x y
  { t with fixed := t.fixed.map (fun z => edge (swap z.1) (swap z.2)),
           point := fun i => swap (t.point i), dest := fun i => swap (t.dest i) }

private def relabel {n : Nat} (s : Equiv.Perm (Fin n)) (e : EdgeWalk.Edge n) := edge (s e.1) (s e.2)

private theorem on_edge {n : Nat} (s : Equiv.Perm (Fin n)) (a b : Fin n) :
    relabel s (edge a b)=edge (s a) (s b) := by
  rcases le_total a b with h|h
  · simp [relabel,edge,min_eq_left h,max_eq_right h]
  · simp [relabel,edge,min_eq_right h,max_eq_left h,min_comm,max_comm]

/-- Exchanging two labels preserves legality and the number of wild edges for every placement. -/
theorem exchange_cost {d r n k b : Nat} (t : Setup d r n k) (x y : Fin n) (p : Perm (Fin d))
    (old : let w := draw t.fixed.toFinset t.point t.dest p; Legal w ∧ w.card=b) :
    let w := (edges (exchange t x y) p).toFinset; Legal w ∧ w.card=b := by
  let s := Equiv.swap x y
  let W := (edges t p).toFinset
  have legal : Legal W := by simpa only [W,actual] using old.1
  have size : W.card=b := by simpa only [W,actual] using old.2
  have eq : edges (exchange t x y) p=(edges t p).map (relabel s) := by
    change t.fixed.map (relabel s) ++ (List.finRange d).map (fun i => edge (s (t.point i)) (s (t.dest (p i)))) =
      (t.fixed ++ (List.finRange d).map (fun i => edge (t.point i) (t.dest (p i)))).map (relabel s)
    simp only [List.map_append,List.map_map,Function.comp_def,on_edge]
  have mapped : ((edges t p).map (relabel s)).toFinset=W.image (relabel s) := by
    ext z
    simp [W]
  rw [eq,mapped]
  change Legal (W.image (relabel s)) ∧ (W.image (relabel s)).card=b
  have ordered (a b : Fin n) (ne : a≠b) : (edge a b).1<(edge a b).2 := by
    rcases lt_or_gt_of_ne ne with h|h <;> simp [edge,min_eq_left,min_eq_right,max_eq_left,max_eq_right,h.le,h]
  refine ⟨?_,?_⟩
  · intro z hz
    obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hz
    exact ordered _ _ (s.injective.ne (legal _ he).ne)
  · rw [Finset.card_image_of_injOn]; exact size
    intro e he f hf h
    have restore (a : EdgeWalk.Edge n) (ha : a∈W) : relabel s.symm (relabel s a)=a := by
      change relabel s.symm (edge (s a.1) (s a.2))=a
      rw [on_edge]
      simp only [s.symm_apply_apply,edge,min_eq_left (legal _ ha).le,max_eq_right (legal _ ha).le,Prod.mk.eta]
    exact (restore e he).symm.trans ((congrArg (relabel s.symm) h).trans (restore f hf))

def successful {d r n k : Nat} (t : Setup d r n k) :=
  ∃ p : Perm (Fin d),Works t.graph (draw t.fixed.toFinset t.point t.dest p)

theorem classify {A : Type} {d r n k : Nat} (t : A → Setup d r n k) (ok : A → Prop)
    (wins : ∀ a,ok a → ∃ p : Perm (Fin d),∀ c,connects (t a) p c=true)
    (losses : ∀ a,¬ok a → ∀ p : Perm (Fin d),∃ c,sealed (t a) p c=true) (a : A) :
    successful (t a) ↔ ok a := by
  classical
  refine ⟨fun ⟨p,win⟩ => ?_,fun yes => ?_⟩
  · by_contra no
    obtain ⟨c,cut⟩ := losses a no p
    exact has_cut (t a) p c cut (win c)
  · obtain ⟨p,yes⟩ := wins a yes
    exact ⟨p,fun c => has_path (t a) p c (yes c)⟩

/-- A base-five code identifies a suggested permutation. Only a permutation
with this code is tested for the positive direction. -/
private def code (p : Perm (Fin 5)) := (List.finRange 5).foldl (fun acc i => 5*acc+(p i).val) 0

theorem by_witness {A : Type} {r n k : Nat} (t : A → Setup 5 r n k) (ok : A → Prop)
    (w : A → Nat)
    (check : ∀ a,ok a → ∃ p : Perm (Fin 5),code p=w a ∧ ∀ c,connects (t a) p c=true)
    (blocked : ∀ a,¬ok a → ∀ p : Perm (Fin 5),∃ c,sealed (t a) p c=true) (a : A) :
    successful (t a) ↔ ok a :=
  classify t ok (fun b hb => by obtain ⟨p,_,win⟩ := check b hb; exact ⟨p,win⟩) blocked a

namespace K15
open WildSlots.Quintet.K15

abbrev Choice := Fin 5 × Fin 10
private def witness (a : Choice) : Nat :=
  let rows : Array (Array Nat) := #[
    #[1646,714,214,422,970,214,242,194,898,566],
    #[1730,214,346,434,222,242,194,298,0,694],
    #[366,414,558,358,1778,1490,414,194,1346,898],
    #[346,194,538,194,582,298,434,214,1366,954],
    #[294,194,198,194,346,294,446,422,2022,970]]
  (rows[a.1.val]!)[a.2.val]!

def changed (a : Choice) := exchange (plan odd) (Fin.ofNat' 15 a.1.val) (Fin.ofNat' 15 (5+a.2.val))
def works (a : Choice) : Prop := a.1≠1 ∨ a.2≠8
instance (a : Choice) : Decidable (works a) := by unfold works; infer_instance

/-- The first coordinate names a free point. Adding five to the second names
the point of a destination group that takes its place. -/
theorem which (a : Choice) : successful (changed a) ↔ works a :=
  by_witness changed works witness (by native_decide) (by native_decide) a

theorem count : (Finset.univ.filter works).card=49 := by decide

theorem cost (a : Choice) (p : Perm (Fin 5)) :
    let w := (edges (changed a) p).toFinset
    Legal w ∧ w.card=10 :=
  exchange_cost _ _ _ p (sharp_odd.1 p)

#print axioms which
end K15

namespace K17
open WildSlots.Quintet.K17

abbrev Choice := Fin 5 × Fin 12
private def witness (a : Choice) : Nat :=
  let rows : Array (Array Nat) := #[
    #[698,694,1294,238,294,214,422,898,1334,214,214,222],
    #[198,194,358,334,346,214,1394,242,294,422,714,214],
    #[238,738,582,482,446,242,422,194,194,898,414,214],
    #[214,334,238,214,542,294,2426,214,214,542,482,242],
    #[334,714,238,742,214,194,446,214,1982,1210,486,238]]
  (rows[a.1.val]!)[a.2.val]!

def changed (a : Choice) := exchange (plan odd) (Fin.ofNat' 17 a.1.val) (Fin.ofNat' 17 (5+a.2.val))
def works (_a : Choice) : Prop := True
instance (a : Choice) : Decidable (works a) := by unfold works; infer_instance

/-- The first coordinate names a free point. Adding five to the second names
the point of a destination group that takes its place. -/
theorem which (a : Choice) : successful (changed a) ↔ works a :=
  by_witness changed works witness (by native_decide) (by native_decide) a

theorem count : (Finset.univ.filter works).card=60 := by decide

theorem cost (a : Choice) (p : Perm (Fin 5)) :
    let w := (edges (changed a) p).toFinset
    Legal w ∧ w.card=12 :=
  exchange_cost _ _ _ p (sharp_odd.1 p)

#print axioms which
end K17

namespace K19
open WildSlots.Quintet.K19

abbrev Choice := Fin 5 × Fin 11
private def witness (a : Choice) : Nat :=
  let rows : Array (Array Nat) := #[
    #[1358,738,2538,1398,2154,482,194,214,358,366,0],
    #[358,238,1138,898,482,414,414,1294,194,358,0],
    #[194,698,738,446,954,214,214,1394,898,214,0],
    #[738,566,346,366,242,194,194,1398,434,242,0],
    #[694,482,334,358,358,194,738,1394,970,238,0]]
  (rows[a.1.val]!)[a.2.val]!

def changed (a : Choice) := exchange (plan odd) (Fin.ofNat' 19 a.1.val) (Fin.ofNat' 19 (5+a.2.val))
def works (a : Choice) : Prop := a.2≠10
instance (a : Choice) : Decidable (works a) := by unfold works; infer_instance

/-- The first coordinate names a free point. Adding five to the second names
the point of a destination group that takes its place. -/
theorem which (a : Choice) : successful (changed a) ↔ works a :=
  by_witness changed works witness (by native_decide) (by native_decide) a

theorem count : (Finset.univ.filter works).card=50 := by decide

theorem cost (a : Choice) (p : Perm (Fin 5)) :
    let w := (edges (changed a) p).toFinset
    Legal w ∧ w.card=13 :=
  exchange_cost _ _ _ p (sharp_odd.1 p)

#print axioms which
end K19

namespace K21
open WildSlots.Quintet.K21

abbrev Choice := Fin 5 × Fin 10
private def witness (a : Choice) : Nat :=
  let rows : Array (Array Nat) := #[
    #[1470,722,222,222,2382,222,1366,1070,194,694],
    #[2146,222,582,722,558,1346,214,198,214,214],
    #[446,446,2014,1646,214,222,194,194,422,434],
    #[2638,894,222,1398,194,222,214,214,482,214],
    #[222,1646,214,1394,214,198,482,222,586,222]]
  (rows[a.1.val]!)[a.2.val]!

def changed (a : Choice) := exchange (plan odd) (Fin.ofNat' 21 a.1.val) (Fin.ofNat' 21 (5+a.2.val))
def works (_a : Choice) : Prop := True
instance (a : Choice) : Decidable (works a) := by unfold works; infer_instance

/-- The first coordinate names a free point. Adding five to the second names
the point of a destination group that takes its place. -/
theorem which (a : Choice) : successful (changed a) ↔ works a :=
  by_witness changed works witness (by native_decide) (by native_decide) a

theorem count : (Finset.univ.filter works).card=50 := by decide

theorem cost (a : Choice) (p : Perm (Fin 5)) :
    let w := (edges (changed a) p).toFinset
    Legal w ∧ w.card=14 :=
  exchange_cost _ _ _ p (sharp_odd.1 p)

#print axioms which
end K21

namespace K23
open WildSlots.Quintet.K23

abbrev Choice := Fin 5 × Fin 12
private def witness (a : Choice) : Nat :=
  let rows : Array (Array Nat) := #[
    #[990,894,2566,1922,1294,242,194,898,222,294,198,194],
    #[298,1454,558,566,294,198,198,542,694,198,194,194],
    #[194,198,1358,346,194,298,298,542,894,346,1394,1394],
    #[698,194,198,222,194,558,298,422,954,294,538,294],
    #[194,194,194,194,222,446,294,1646,1470,298,566,298]]
  (rows[a.1.val]!)[a.2.val]!

def changed (a : Choice) := exchange (plan odd) (Fin.ofNat' 23 a.1.val) (Fin.ofNat' 23 (5+a.2.val))
def works (_a : Choice) : Prop := True
instance (a : Choice) : Decidable (works a) := by unfold works; infer_instance

/-- The first coordinate names a free point. Adding five to the second names
the point of a destination group that takes its place. -/
theorem which (a : Choice) : successful (changed a) ↔ works a :=
  by_witness changed works witness (by native_decide) (by native_decide) a

theorem count : (Finset.univ.filter works).card=60 := by decide

theorem cost (a : Choice) (p : Perm (Fin 5)) :
    let w := (edges (changed a) p).toFinset
    Legal w ∧ w.card=16 :=
  exchange_cost _ _ _ p (sharp_odd.1 p)

#print axioms which
end K23

end WildSlots.Replacement
