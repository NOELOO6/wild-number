import ThirdData
import PairFrames
namespace WildExact.Seventeen
open WildExact
set_option maxRecDepth 10000

def partialState (i : Fin 15) (freq : Array Nat) (r : Row 17) := r.foldr (extend i freq) start
def masks (r : Row 17) := r.map edgeMask
def candidates (r : Row 17) := unions 2 (masks r) ++ unions 3 (masks r) ++ unions 4 (masks r)
def edgeFee (i : Fin 15) (r : Row 17) := (r.map (fun e => price i e.1 e.2)).sum

private theorem countMore_eq (f : Array Nat) (m) (xs : List Nat) (base) :
    countMore f m xs base=base+(xs.map (fun t => valueAt f (m ||| t))).sum := by
  induction xs generalizing base with
  | nil => simp [countMore]
  | cons x xs ih => change countMore f m xs (base+_) = _; rw [ih]; exact Nat.add_assoc ..

theorem partial_shape (i : Fin 15) (f : Array Nat) (r : Row 17) :
    (partialState i f r).row=r ∧ (partialState i f r).singles=unions 1 (masks r) ∧
    (partialState i f r).pairs=unions 2 (masks r) ∧ (partialState i f r).triples=unions 3 (masks r) ∧
    (partialState i f r).charge=edgeFee i r := by
  induction r with
  | nil => simp [partialState,start,masks,unions,edgeFee]
  | cons e r ih =>
    obtain ⟨a,b,c,d,p⟩ := ih
    change (extend i f e (partialState i f r)).row=_ ∧ _
    simp only [partialState,List.foldr_cons] at *
    simp [extend,masks,unions,edgeFee,a,b,c,d,p,Int.add_comm] at *

theorem partial_cost (i : Fin 15) (f : Array Nat) (r : Row 17) :
    (partialState i f r).cost=((candidates r).map (valueAt f)).sum := by
  induction r with
  | nil => rfl
  | cons e r ih =>
    obtain ⟨_,b,c,d,_⟩ := partial_shape i f r
    have prev := ih
    simp only [candidates,masks,List.map_append,List.sum_append] at prev
    change (extend i f e (partialState i f r)).cost=_
    simp only [extend,countMore_eq,ih,b,c,d,candidates,masks,List.map_cons,unions,
      List.map_append,List.sum_append,List.map_map,Function.comp_def]
    simp only [Nat.reduceAdd] at *
    omega

private theorem inspect_sound (i : Fin 15) (f : Array Nat) (lo : Int) (k old : Nat)
    (xs : List V) (acc m : Row 17) (hm : m∈enumerate old xs) (good : ∀ e∈m, allowedThird i e.1 e.2=true)
    (len : xs.length≤2*k) (nd : xs.Nodup)
    (ok : inspect i f lo k xs (partialState i f acc)=true) :
    permits i lo (partialState i f (m.reverse++acc))=true := by
  induction k generalizing old xs acc m with
  | zero =>
    have eq : xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    cases old <;> simp [enumerate] at hm <;> subst m <;> exact ok
  | succ k ih =>
    cases xs with
    | nil => cases old <;> simp [enumerate] at hm <;> subst m <;> exact ok
    | cons x xs =>
      cases old with
      | zero => simp [enumerate] at hm
      | succ old =>
        obtain ⟨y,hy,t⟩ := List.mem_flatMap.mp hm
        obtain ⟨m,mem,rfl⟩ := List.mem_map.mp t
        have take := List.all_eq_true.mp ok y hy
        have allow := good (x,y) (by simp)
        simp only [allow,Bool.not_true,Bool.false_or] at take
        have uniq := (List.nodup_cons.mp nd).2
        have size : (xs.filter (· != y)).length=xs.length-1 := by rw [←uniq.erase_eq_filter y,List.length_erase_of_mem hy]
        have pos := List.length_pos_of_mem hy
        have room : (xs.filter (· != y)).length≤2*k := by simp only [List.length_cons] at len; omega
        simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using
          ih old (xs.filter (· != y)) ((x,y)::acc) m mem (fun e h => good e (by simp [h])) room (uniq.filter _) take

private theorem value_min (i j k : Fin 15) : minTransfer i ≤ transfer i j k := by
  exact (show ∀ (i j k : Fin 15),minTransfer i≤transfer i j k from by native_decide) i j k

set_option maxHeartbeats 1500000
theorem closed_price (i : Fin 15) (f : V → V) (inv : Function.Involutive f)
    (diffA : ∀ x, refA.get x ≠ f x) (diffB : ∀ x, (refB.get i).get x ≠ f x)
    (m : Row 17) (mem : m∈Rows 17) (owns : Respects f m) (cert : certified i=true) :
    2*((((candidates m.reverse).map (valueAt (stats refA.get (refB.get i).get).frequency)).sum : Nat) : Int) ≤
      edgeFee i m.reverse + transfer i (typeOf refA.get f) (typeOf (refB.get i).get f) := by
  let freq := (stats refA.get (refB.get i).get).frequency
  have allowed (e) (h : e∈m) : allowedThird i e.1 e.2=true := by
    simp [allowedThird,← owns e h,diffA,diffB]
  change (_ && inspect i freq (minTransfer i) 9 (List.finRange 18) start)=true at cert
  have checked := (Bool.and_eq_true_iff.mp cert).2
  have res := inspect_sound i freq (minTransfer i) 9 18 (List.finRange 18) [] m mem allowed
    (by decide) (List.nodup_finRange _) checked
  rw [List.append_nil] at res
  have cover (x : V) : lookup m.reverse x=f x := by
    apply lookup_agrees f inv _ (fun e h => owns e (List.mem_reverse.mp h))
    obtain ⟨y,cov⟩ := cover_node _ _ m mem x (List.mem_finRange x)
    rcases Bool.or_eq_true_iff.mp cov with l|l
    · exact ⟨(x,y),List.mem_reverse.mpr (List.contains_iff_mem.mp l),Or.inl rfl⟩
    · exact ⟨(y,x),List.mem_reverse.mpr (List.contains_iff_mem.mp l),Or.inr rfl⟩
  have tab : (Vector.ofFn (lookup m.reverse)).get=f := by
    funext x; exact (Vector.getElem_ofFn x.isLt).trans (cover x)
  obtain ⟨row,_,_,_,fee⟩ := partial_shape i freq m.reverse
  simp only [permits,partial_cost,fee,row,tab] at res
  split at res
  next h => have := value_min i (typeOf refA.get f) (typeOf (refB.get i).get f); dsimp [freq] at h; omega
  next => have h := of_decide_eq_true res; dsimp [freq] at h; omega

end WildExact.Seventeen
