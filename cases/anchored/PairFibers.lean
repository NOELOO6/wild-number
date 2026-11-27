import UniformCuts

namespace WildAnchor
open Finset
variable {I : Type} [Fintype I] [DecidableEq I]

abbrev State (I : Type) := I → Bool × Bool
abbrev Shuffle (I : Type) := Equiv.Perm I × (I → Bool)

def flip (b : Bool) (x : Bool × Bool) : Bool × Bool := if b then x.swap else x
def kind (x : Bool × Bool) : Fin 3 := if x.1 then (if x.2 then 2 else 1) else (if x.2 then 1 else 0)
def Fits (q : Shuffle I) (s t : State I) : Prop := ∀ i, flip (q.2 i) (s i)=t (q.1 i)
instance (q : Shuffle I) (s t : State I) : Decidable (Fits q s t) := inferInstanceAs (Decidable (∀ _,_))
def width (s : State I) (j : Fin 3) := (univ.filter fun i => kind (s i)=j).card
def price (s t : State I) := if ∀ j,width s j=width t j then
  (∏ j : Fin 3,(width s j).factorial) * 2^(width s 0+width s 2) else 0

private theorem kind_flip (x : Bool × Bool) (b : Bool) : kind (flip b x)=kind x := by
  rcases x with ⟨a,c⟩; cases a <;> cases c <;> cases b <;> decide
private theorem fixed_bit (x : Bool × Bool) (j k : Bool) (h : kind x=1)
    (same : flip j x=flip k x) : j=k := by
  revert h same; rcases x with ⟨a,c⟩; cases a <;> cases c <;> cases j <;> cases k <;> decide

/-- Number of pair permutations and independent endpoint flips that carry
one specified side onto another. The three fibers have zero, one or two
selected endpoints. A split pair forces the orientation of its flip. -/
theorem fiber_price (s t : State I) :
    (univ.filter fun q : Shuffle I => Fits q s t).card ≤ price s t := by
  classical
  let K (a : State I) (j : Fin 3) := {i : I // kind (a i)=j}
  let Ω := {q : Shuffle I // Fits q s t}
  have preserve (q : Ω) (i : I) : kind (s i)=kind (t (q.val.1 i)) := by
    rw [← q.property i,kind_flip]
  let part (q : Ω) (j : Fin 3) : K s j ≃ K t j :=
    q.val.1.subtypeEquiv (fun i => by rw [preserve q i])
  let R := {i : I // kind (s i)≠1}
  let encode (q : Ω) := ((fun j => part q j),fun i : R => q.val.2 i.val)
  have inj : Function.Injective encode := by
    intro q p h
    have e : q.val.1=p.val.1 := by
      ext i
      let j := kind (s i)
      exact congrArg (fun v => ((v.1 j ⟨i,rfl⟩ : K t j) : I)) h
    apply Subtype.ext
    apply Prod.ext e
    funext i
    by_cases one : kind (s i)=1
    · apply fixed_bit _ _ _ one
      rw [q.property,p.property,e]
    · exact congrArg (fun v => v.2 (⟨i,one⟩ : R)) h
  have size (a : State I) (j : Fin 3) : Fintype.card (K a j)=width a j := Fintype.card_subtype _
  have left : Fintype.card Ω=(univ.filter fun q : Shuffle I => Fits q s t).card := Fintype.card_subtype _
  by_cases non : Nonempty Ω
  · obtain ⟨q⟩ := non
    have eq (j : Fin 3) : width s j=width t j := by
      rw [←size,←size]; exact Fintype.card_congr (part q j)
    have parts (j : Fin 3) : Fintype.card (K s j ≃ K t j)=(width s j).factorial := by
      rw [Fintype.card_equiv (part q j),size]
    have rem : Fintype.card R=width s 0+width s 2 := by
      rw [Fintype.card_subtype]
      let A := univ.filter fun i => kind (s i)=0
      let B := univ.filter fun i => kind (s i)=2
      have ds : Disjoint A B := disjoint_left.mpr (fun _ ha hb =>
        (by decide : (0 : Fin 3)≠2) ((mem_filter.mp ha).2.symm.trans (mem_filter.mp hb).2))
      have un : (univ.filter fun i => kind (s i)≠1)=A∪B := by
        ext i
        simp only [A,B,mem_union,mem_filter,mem_univ,true_and]
        have h := (kind (s i)).isLt
        omega
      rw [un,card_union_of_disjoint ds]
      rfl
    have upper := Fintype.card_le_of_injective encode inj
    rw [left,Fintype.card_prod,Fintype.card_pi,Fintype.card_fun,Fintype.card_bool,rem] at upper
    simpa only [price,if_pos eq,parts] using upper
  · have zero := Fintype.card_eq_zero_iff.mpr ⟨fun x => non ⟨x⟩⟩
    rw [←left,zero]
    exact Nat.zero_le _

end WildAnchor
