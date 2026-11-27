import CutSemantics
import Mathlib.Data.Fintype.BigOperators
namespace WildExact.Seventeen

def natTotal {α} (xs : List α) (f : α → Nat) := (xs.map f).sum
def score (f : Layout → Nat) := natTotal (List.finRange 6188) (fun b => natTotal (List.finRange 15400) (fun p => f (b,p)))

theorem selected_filter (s : Nat) : selected s = (List.finRange 15400).filter (fun p => s.testBit p.val) := by
  have all : (List.finRange 280).flatMap bucket = List.finRange 15400 := by native_decide
  rw [←all,List.filter_flatMap]
  unfold selected
  apply List.flatMap_congr
  intro i hi
  let word := (s >>> (55*i.val)) &&& ((1 <<< 55)-1)
  have bits (p : Small) (h : p∈bucket i) : word.testBit (p.val%55)=s.testBit p.val := by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
    have hj := j.isLt
    simp only [word,Nat.testBit_and,Nat.testBit_shiftRight,Nat.one_shiftLeft,Nat.testBit_two_pow_sub_one]
    have eq : (55*i.val+j.val)%55=j.val := by omega
    simp only [eq,hj,decide_true,Bool.and_true]
  change (if word=0 then [] else (bucket i).filter (fun p => word.testBit (p.val%55)))=_
  split
  next zero =>
    symm
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    rw [←bits p hp,zero,Nat.zero_testBit]
    decide
  next => exact List.filter_congr (fun p h => bits p h)

def lost (f : V → V) (l : Layout) := (badBits (closedTable f) l.1).testBit l.2.val
theorem lost_spec (f : V → V) (l : Layout) : lost f l=true ↔ Loss f l := bit_loss f l.1 l.2

theorem together_filter (a b : V → V) (i : Big) : together (closedTable a) (closedTable b) i =
    (List.finRange 15400).filter (fun p => lost a (i,p) && lost b (i,p)) := by
  simp only [together,selected_filter,Nat.testBit_and,lost]

theorem count_as_total {α} (xs : List α) (b : α → Bool) :
    (xs.filter b).length=natTotal xs (fun x => if b x then 1 else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : b x <;> simp [List.filter_cons,hx,natTotal] at ih ⊢ <;> omega

theorem filter_total {α} (xs : List α) (b : α → Bool) (f : α → Nat) :
    natTotal (xs.filter b) f=natTotal xs (fun x => if b x then f x else 0) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hx : b x <;> simp [List.filter_cons,hx,natTotal] at ih ⊢ <;> omega

theorem single_identity (a : V → V) :
    oneCount (closedTable a)=score (fun l => if lost a l then 1 else 0) := by
  simp only [oneCount,score,natTotal]
  apply congrArg List.sum
  apply List.map_congr_left
  intro b _
  rw [selected_filter]
  exact count_as_total ..

def shared (a b : V → V) (l : Layout) := lost a l && lost b l
def sides (l : Layout) := (localCuts l.2).map (embed l.1)

theorem double_identity (a b : V → V) :
    (stats a b).both=score (fun l => if shared a b l then 1 else 0) := by
  let step := reportBig (closedTable a) (closedTable b)
  have aux (xs : List Big) (start : Tally) :
      (xs.foldl step start).both=start.both + natTotal xs (fun i =>
        natTotal (List.finRange 15400) (fun p => if shared a b (i,p) then 1 else 0)) := by
    induction xs generalizing start with
    | nil => simp [natTotal]
    | cons x xs ih =>
      rw [List.foldl_cons,ih]
      simp only [step,reportBig,together_filter,count_as_total,shared,natTotal,List.map_cons,List.sum_cons]
      exact Nat.add_assoc ..
  simpa only [stats,step,blank,Nat.zero_add,score] using aux (List.finRange 6188) blank

private theorem fold_cuts (t : Array Nat) (ss : List Nat) (s : Nat) (h : s<t.size) :
    (ss.foldl addCut t).size=t.size ∧ (ss.foldl addCut t)[s]?.getD 0=t[s]?.getD 0+ss.count s := by
  induction ss generalizing t with
  | nil => simp
  | cons x xs ih =>
    have sz : (addCut t x).size=t.size := by simp [addCut]
    obtain ⟨old,val⟩ := ih (addCut t x) (by simpa [sz] using h)
    refine ⟨old.trans sz,?_⟩
    rw [List.foldl_cons,val]
    by_cases eq : x=s
    · subst x
      simp [addCut,Array.getElem?_modify,Array.getElem?_eq_getElem h,Nat.add_comm,Nat.add_assoc,Nat.add_left_comm]
    · simp [addCut,Array.getElem?_modify,eq,List.count_cons,Ne.symm eq]

private theorem local_frequency (i : Big) (p : Small) (s : Nat) (t : Array Nat) (h : s<t.size) :
    (reportLocal i t p).size=t.size ∧ (reportLocal i t p)[s]?.getD 0=t[s]?.getD 0+(sides (i,p)).count s := by
  simpa only [reportLocal,sides,List.foldl_map] using fold_cuts t (sides (i,p)) s h

private theorem big_frequency (i : Big) (ps : List Small) (s : Nat) (t : Array Nat) (h : s<t.size) :
    (ps.foldl (reportLocal i) t).size=t.size ∧
    (ps.foldl (reportLocal i) t)[s]?.getD 0=t[s]?.getD 0+natTotal ps (fun p => (sides (i,p)).count s) := by
  induction ps generalizing t with
  | nil => simp [natTotal]
  | cons p ps ih =>
    obtain ⟨sz,val⟩ := local_frequency i p s t h
    obtain ⟨su,v⟩ := ih (reportLocal i t p) (by simpa [sz] using h)
    simp only [List.foldl_cons] at *
    refine ⟨su.trans sz,?_⟩
    exact v.trans ((congrArg (fun u => u+natTotal ps (fun q => (sides (i,q)).count s)) val).trans (Nat.add_assoc ..))

/-- For a particular vertex subset, the certificate frequency counts its occurrences among the sides of layouts where both colors fail. -/
theorem frequency_identity (a b : V → V) (s : Nat) (bound : s<262144) :
    (stats a b).frequency[s]?.getD 0=score (fun l => if shared a b l then (sides l).count s else 0) := by
  let step := reportBig (closedTable a) (closedTable b)
  have aux (xs : List Big) (t : Tally) (h : s<t.frequency.size) :
      (xs.foldl step t).frequency[s]?.getD 0=t.frequency[s]?.getD 0+natTotal xs (fun i =>
        natTotal (List.finRange 15400) (fun p => if shared a b (i,p) then (sides (i,p)).count s else 0)) := by
    induction xs generalizing t with
    | nil => simp [natTotal]
    | cons i xs ih =>
      have ⟨sz,v⟩ := big_frequency i (together (closedTable a) (closedTable b) i) s t.frequency h
      change (step t i).frequency.size=t.frequency.size at sz
      change (step t i).frequency[s]?.getD 0=_ at v
      rw [together_filter,filter_total] at v
      rw [List.foldl_cons,ih (step t i) (by simpa [sz] using h),v]
      simp [natTotal,shared,Nat.add_assoc]
  simpa [stats,score,blank,bound] using aux (List.finRange _) blank (by simpa [blank] using bound)

private theorem total_univ {n : Nat} (f : Fin n → Nat) : natTotal (List.finRange n) f = ∑ i,f i := by
  rw [natTotal,←List.sum_toFinset _ (List.nodup_finRange _),List.toFinset_finRange]

theorem score_univ (f : Layout → Nat) : score f=∑ l,f l := by
  unfold score
  simp_rw [total_univ]
  exact (Fintype.sum_prod_type f).symm

theorem score_transport (e : Equiv.Perm Layout) (f g : Layout → Nat) (eq : ∀ l,g (e l)=f l) : score f=score g := by
  simp only [score_univ]
  simpa only [eq] using Equiv.sum_comp e g

end WildExact.Seventeen
