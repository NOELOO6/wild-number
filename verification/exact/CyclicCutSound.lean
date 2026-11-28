import CyclicCuts
import RotationalLayouts

namespace WildExact.Rotation.CutTest
open WildDeletion EdgeWalk

variable {n : Nat}
local notation "E" => Edge (n+1)

private theorem selected_union (bs : Blocks n) (p : List (V n) → Bool) :
    (bs.filter p).flatten ∈ unions bs := by
  induction bs with
  | nil => simp [unions]
  | cons B bs ih =>
    by_cases h : p B=true
    · simp only [List.filter_cons_of_pos h,List.flatten_cons,unions,List.mem_append]
      exact Or.inr (List.mem_map.mpr ⟨_,ih,rfl⟩)
    · simp only [List.filter_cons_of_neg h,unions,List.mem_append]
      exact Or.inl ih

private theorem label_at (ss : List (List (V n))) (x : V n) (i : Nat) (hi : i<ss.length) :
    (labels x ss).testBit i = decide (x∈ss[i]) := by
  induction ss generalizing i with
  | nil => simp at hi
  | cons S ss ih =>
    cases i with
    | zero =>
      by_cases h : x∈S <;> simp [labels,h,Nat.testBit_zero,Nat.add_mod]
    | succ i =>
      rw [Nat.testBit_succ]
      have h : labels x (S::ss)/2=labels x ss := by
        change (2*labels x ss + (if x∈S then 1 else 0))/2=labels x ss
        split <;> omega
      rw [h]
      exact ih _ (by simpa using hi)

private theorem translated_at (ss : List (List (V n))) (c x : V n) :
    (translated ss c)[x.val]! = labels (x+c) ss := by
  have h : x.val<(translated ss c).size := by simp [translated]
  rw [getElem!_pos (c:=translated ss c) (i:=x.val) h]
  simp [translated]

private theorem untouched (bits : Array Nat) (i : Nat) (es : List E)
    (none : ∀ e∈es,(bits[e.1.val]!).testBit i=(bits[e.2.val]!).testBit i) :
    (crossed bits es).testBit i=false := by
  have same (xs : List E) (a : Nat)
      (ok : ∀ e∈xs,(bits[e.1.val]!).testBit i=(bits[e.2.val]!).testBit i) :
      (xs.foldl (fun mask e => mask ||| (bits[e.1.val]! ^^^ bits[e.2.val]!)) a).testBit i=a.testBit i := by
    induction xs generalizing a with
    | nil => rfl
    | cons e xs ih =>
      rw [List.foldl_cons,ih _ (fun q h => ok q (List.mem_cons_of_mem _ h))]
      simp [Nat.testBit_or,Nat.testBit_xor,ok e (List.mem_cons_self ..)]
  simpa [crossed] using same es 0 none

/-- Any two vertices in one block are joined by the star drawn on it. -/
theorem block_walk (bs : Blocks n) (B : List (V n)) (hb : B∈bs) (es : List E)
    (x y : V n) (hx : x∈B) (hy : y∈B) : Walk (Adj (drawing bs++es)) x y := by
  cases B with
  | nil => simp at hx
  | cons r rs =>
    have path (v : V n) (hv : v∈r::rs) : Walk (Adj (drawing bs++es)) r v := by
      rcases List.mem_cons.mp hv with rfl|h
      · exact .stay _
      · exact .step (.stay _) (Or.inl (List.mem_append_left _ (List.mem_flatMap.mpr
          ⟨r::rs,hb,List.mem_map.mpr ⟨v,h,rfl⟩⟩)))
    exact (backwards (fun h => h.symm) (path x hx)).join (path y hy)

/-- A symmetric graph that connects each block and crosses every cut
of whole blocks is connected. -/
theorem connected_of_crossings (bs : Blocks n) (cover : ∀ x : V n,x∈bs.flatten)
    (R : V n → V n → Prop) (sym : ∀ {x y},R x y → R y x)
    (inside : ∀ B∈bs,∀ x y : V n,x∈B → y∈B → Walk R x y)
    (crossing : ∀ S∈cuts bs,∃ x y,R x y ∧ ¬(x∈S ↔ y∈S)) : Connected R := by
  classical
  suffices reaches : ∀ x, Walk R 0 x from fun x y => (backwards (R:=R) sym (reaches x)).join (reaches y)
  intro x
  apply Classical.byContradiction
  intro out
  let bsOut (B : List (V n)) := B.any fun y => decide (¬Walk R 0 y)
  let S := (bs.filter bsOut).flatten
  let ss := cuts bs
  have mem (v : V n) : v∈S ↔ ¬Walk R 0 v := by
    constructor
    · intro hv reach
      obtain ⟨B,hB,vB⟩ := List.mem_flatten.mp hv
      obtain ⟨hb,hit⟩ := List.mem_filter.mp hB
      obtain ⟨z,zb,outside⟩ := List.any_eq_true.mp hit
      exact of_decide_eq_true outside (reach.join (inside B hb v z vB zb))
    · intro away
      obtain ⟨B,hb,hin⟩ := List.mem_flatten.mp (cover v)
      exact List.mem_flatten.mpr ⟨B,List.mem_filter.mpr
        ⟨hb,List.any_eq_true.mpr ⟨v,hin,decide_eq_true away⟩⟩,hin⟩
  have xS := (mem x).mpr out
  have root : (0 : V n)∉S := fun h => (mem 0).mp h (.stay _)
  have hS : S∈ss := by
    apply List.mem_filter.mpr ⟨selected_union bs bsOut,?_⟩
    change (!S.isEmpty && !S.contains 0)=true
    have nonempty : S≠[] := fun e => by simp [e] at xS
    exact Bool.and_eq_true_iff.mpr ⟨by simpa only [Bool.not_eq_true',List.isEmpty_eq_false_iff] using nonempty, by simpa using root⟩
  obtain ⟨u,v,edge,diff⟩ := crossing S hS
  apply diff
  rw [mem,mem]
  exact not_congr ⟨fun h => h.step edge,fun h => h.step (sym edge)⟩

/-- Each tested bit is a union of whole wild blocks. If every such side
has a crossing matching edge, all vertices are reachable. -/
theorem connected_row (bs : Blocks n) (cover : ∀ x : V n,x∈bs.flatten) (es : List E)
    (c : V n) (found : crossed (translated (cuts bs) c) es=2^(cuts bs).length-1) : Connected (Adj (drawing bs++shift es c)) := by
  classical
  let R := Adj (drawing bs++shift es c)
  apply connected_of_crossings bs cover R (fun h => Or.symm h) (fun B h => block_walk bs B h _)
  intro S hS
  by_contra! none
  let ss := cuts bs
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hS
  change i<ss.length at hi
  have eqbit (e : E) (he : e∈es) :
      ((translated ss c)[e.1.val]!).testBit i=((translated ss c)[e.2.val]!).testBit i := by
    rw [translated_at,translated_at,label_at _ _ _ hi,label_at _ _ _ hi,eq]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact none _ _ (Or.inl (List.mem_append_right _ (List.mem_map.mpr ⟨e,he,rfl⟩)) :
      R (e.1+c) (e.2+c))
  have no := untouched (translated ss c) i es eqbit
  change crossed (translated ss c) es=2^ss.length-1 at found
  simp [found,Nat.testBit_two_pow_sub_one,hi] at no

theorem connected (bs : Blocks n) (cover : ∀ x : V n,x∈bs.flatten) (es : List E)
    (ok : pass (table bs) es=true) (c : V n) : Connected (Adj (drawing bs++shift es c)) :=
  connected_row bs cover es c (beq_iff_eq.mp (List.all_eq_true.mp ok (translated (cuts bs) c)
    (List.mem_map.mpr ⟨c,List.mem_finRange c,rfl⟩)))

end WildExact.Rotation.CutTest
