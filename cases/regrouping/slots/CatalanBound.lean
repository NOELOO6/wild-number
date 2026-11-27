import PaletteSizes
import Mathlib.Combinatorics.Enumerative.DyckWord

namespace WildSlots
namespace Records
open Finset DyckStep
variable {n : Nat}

/-- One plus the largest value read up to and including position i. -/
private def height (p : Perm (Fin n)) (i : Fin n) :=
  (univ.filter (fun j => j ≤ i)).sup (fun j => (p j).val+1)

private theorem at_le (p : Perm (Fin n)) {i j : Fin n} (h : j ≤ i) : (p j).val+1 ≤ height p i :=
  Finset.le_sup (s:=univ.filter (fun x => x ≤ i)) (f:=fun x => (p x).val+1) (b:=j) (mem_filter.mpr ⟨mem_univ _,h⟩)

private theorem high_le (p : Perm (Fin n)) (i : Fin n) : height p i ≤ n :=
  Finset.sup_le (fun j _ => (p j).isLt)

private theorem height_mono (p : Perm (Fin n)) : Monotone (height p) := by
  intro i j ij
  exact sup_mono (fun t ht => mem_filter.mpr ⟨mem_univ _,le_trans (mem_filter.mp ht).2 ij⟩)

private theorem lower (p : Perm (Fin n)) (i : Fin n) : i.val+1 ≤ height p i := by
  let f (x : Fin (i.val+1)) : Fin (height p i) :=
    ⟨(p (x.castLE i.isLt)).val,at_le p (by exact Nat.le_of_lt_succ x.isLt)⟩
  have inj : Function.Injective f := fun x y eq => by
    have vals : (p (x.castLE i.isLt)).val=(p (y.castLE i.isLt)).val := congrArg (fun t : Fin (height p i) => t.val) eq
    have h := p.injective (Fin.ext vals)
    exact Fin.ext (congrArg (fun t : Fin n => t.val) h)
  simpa using Fintype.card_le_of_injective f inj

private theorem no_first_difference {p q : Perm (Fin n)} (ok : avoids q) (i : Fin n)
    (before : ∀ j < i,p j=q j) (same : height p i=height q i) (smaller : p i < q i) : False := by
  have ne : (univ.filter (fun j : Fin n => j ≤ i)).Nonempty := ⟨i,by simp⟩
  obtain ⟨j,hj,big⟩ := exists_mem_eq_sup _ ne (fun j => (p j).val+1)
  change height p i=_ at big
  have ge := at_le q (le_refl i)
  rw [←same,big] at ge
  have ji : j < i := lt_of_le_of_ne (mem_filter.mp hj).2 (by
    rintro rfl
    exact (Nat.not_le_of_lt smaller) (Nat.le_of_succ_le_succ ge))
  have down : q i < q j := lt_of_le_of_ne (by rw [←before j ji];exact Nat.le_of_succ_le_succ ge)
    (fun eq => ji.ne (q.injective eq).symm)
  let k := q.symm (p i)
  have val : q k=p i := q.apply_symm_apply _
  have ik : i < k := by
    rcases lt_trichotomy i k with hit|eq|lt
    · exact hit
    · exact (smaller.ne (val.symm.trans (congrArg q eq.symm))).elim
    · exact (lt.ne (p.injective ((before k lt).trans val))).elim
  exact ok j i k ji ik down (val ▸ smaller)

private theorem records_inj {p q : Perm (Fin n)} (hp : avoids p) (hq : avoids q)
    (same : ∀ i,height p i=height q i) : p=q := by
  classical
  by_contra neq
  let diff := univ.filter (fun i => p i ≠ q i)
  have nonempty : diff.Nonempty := by
    by_contra! h
    exact neq (Equiv.ext (fun i => Classical.byContradiction (fun ne => h ⟨i,mem_filter.mpr ⟨mem_univ _,ne⟩⟩)))
  let i := diff.min' nonempty
  have hi := (mem_filter.mp (min'_mem diff nonempty)).2
  have before (j) (lt : j < i) : p j=q j := by
    exact Classical.byContradiction (fun ne => (not_le_of_gt lt) (min'_le diff j (mem_filter.mpr ⟨mem_univ _,ne⟩)))
  rcases lt_or_gt_of_ne hi with lt|gt
  · exact no_first_difference hq i before (same i) lt
  · exact no_first_difference hp i (fun j hj => (before j hj).symm) (same i).symm gt

private def position (p : Perm (Fin n)) (i : Fin n) := i.val+height p i
private theorem rising (p : Perm (Fin n)) : StrictMono (position p) :=
  fun _ _ h => Nat.add_lt_add_of_lt_of_le h (height_mono p h.le)
private def downs (p : Perm (Fin n)) := univ.image (position p)
private theorem downs_card (p : Perm (Fin n)) : (downs p).card=n := by
  simp [downs,card_image_of_injective _ (rising p).injective]
private theorem below (p : Perm (Fin n)) : downs p ⊆ range (2*n) := by
  intro j hj
  obtain ⟨i,_,rfl⟩ := mem_image.mp hj
  have := high_le p i
  have := i.isLt
  simp only [mem_range,position]
  omega

private theorem ballot (p : Perm (Fin n)) (l : Nat) : ((range l) ∩ downs p).card ≤ l/2 := by
  let early := univ.filter (fun i : Fin n => i.val < l/2)
  have sub : (range l) ∩ downs p ⊆ early.image (position p) := by
    intro j hj
    obtain ⟨inrange,mem⟩ := mem_inter.mp hj
    obtain ⟨i,_,rfl⟩ := mem_image.mp mem
    have bound := lower p i
    have stop : i.val+height p i < l := mem_range.mp inrange
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,by omega⟩,rfl⟩
  have cap := card_le_card_of_injOn (s:=early) (t:=range (l/2)) Fin.val
    (fun i hi => mem_range.mpr (mem_filter.mp hi).2) (fun _ _ _ _ eq => Fin.ext eq)
  exact (card_le_card sub).trans (card_image_le.trans (by simpa using cap))

private def letter (s : Finset Nat) (i : Nat) := if i ∈ s then D else U
private def tape (s : Finset Nat) (l : Nat) := (List.range l).map (letter s)

private theorem count_down (s : Finset Nat) (l : Nat) : (tape s l).count D=((range l) ∩ s).card := by
  induction l with
  | zero => simp [tape]
  | succ l ih =>
    by_cases hit : l ∈ s <;>
      simp_all [tape,List.range_succ,range_add_one,letter,insert_inter_of_mem,insert_inter_of_not_mem]

private theorem counts (s : Finset Nat) (l : Nat) : (tape s l).count U+(tape s l).count D=l := by
  induction l with
  | zero => simp [tape]
  | succ l ih =>
    by_cases hit : l ∈ s <;> simp_all [tape,List.range_succ,letter] <;> omega

private def path (p : Perm (Fin n)) : DyckWord where
  toList := tape (downs p) (2*n)
  count_U_eq_count_D := by
    have total := counts (downs p) (2*n)
    have cnt := count_down (downs p) (2*n)
    rw [inter_eq_right.mpr (below p),downs_card] at cnt
    omega
  count_D_le_count_U i := by
    have firstSteps : (tape (downs p) (2*n)).take i=tape (downs p) (min i (2*n)) := by
      simp only [tape,←List.map_take,List.take_range]
    rw [firstSteps]
    have cap := ballot p (min i (2*n))
    rw [←count_down] at cap
    have total := counts (downs p) (min i (2*n))
    omega

private theorem length_path (p : Perm (Fin n)) : (path p).semilength=n := by
  rw [DyckWord.semilength,(path p).count_U_eq_count_D]
  change (tape _ _).count D=n
  rw [count_down,inter_eq_right.mpr (below p),downs_card]

private theorem path_inj {p q : Perm (Fin n)} (hp : avoids p) (hq : avoids q)
    (eq : path p=path q) : p=q := by
  have words := congrArg DyckWord.toList eq
  change tape (downs p) (2*n)=tape (downs q) (2*n) at words
  have sets : downs p=downs q := by
    ext j
    by_cases lt : j < 2*n
    · have e := congrArg (fun L : List DyckStep => L[j]?) words
      have val : letter (downs p) j=letter (downs q) j := by
        simpa [tape,List.getElem?_map,List.getElem?_range,lt] using e
      by_cases m : j ∈ downs p <;> by_cases k : j ∈ downs q <;> simp_all [letter]
    · exact iff_of_false (fun h => lt (mem_range.mp (below p h))) (fun h => lt (mem_range.mp (below q h)))
  have ranges : Set.range (position p)=Set.range (position q) := by
    simpa [downs] using congrArg (fun s : Finset Nat => (s : Set Nat)) sets
  have pos := ((rising p).range_inj (rising q)).mp ranges
  exact records_inj hp hq (fun i => Nat.add_left_cancel (congrFun pos i))

/-- Recording the successive maxima injects 321-avoiding permutations into
balanced paths with n upward and n downward steps. -/
theorem count_le_catalan (n : Nat) : (sample n).card ≤ catalan n := by
  let f (p : ↥(sample n)) : {w : DyckWord // w.semilength=n} := ⟨path p.val,length_path _⟩
  have inj : Function.Injective f := fun p q eq =>
    Subtype.ext (path_inj (mem_filter.mp p.property).2 (mem_filter.mp q.property).2 (congrArg Subtype.val eq))
  simpa [DyckWord.card_dyckWord_semilength_eq_catalan] using Fintype.card_le_of_injective f inj
end Records

open Finset WildExact WildDeletion

private theorem middle_growth (n : Nat) : (n+1).choose ((n+1)/2) ≤ 2 * n.choose (n/2) := by
  cases eq : (n+1)/2 with
  | zero =>
    simp only [Nat.choose_zero_right]
    have h := Nat.choose_le_middle 0 n
    rw [Nat.choose_zero_right] at h
    omega
  | succ k =>
    rw [Nat.choose_succ_succ]
    have h := Nat.choose_le_middle k n
    have h' := Nat.choose_le_middle k.succ n
    omega

private theorem catalan_growth (n : Nat) (h : 0 < n) : 2*catalan n ≤ catalan (n+1) := by
  let a : Fin (n+1) := 0
  let b := Fin.last n
  have ab : a ≠ b := by
    intro eq
    have e : 0=n := congrArg (fun t : Fin (n+1) => t.val) eq
    omega
  rw [catalan_succ]
  have sub := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun i : Fin (n+1) => catalan i*catalan (n-i))
    (subset_univ ({a,b} : Finset (Fin (n+1)))) (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_pair ab] at sub
  simpa [a,b,catalan_zero,two_mul] using sub

private theorem middle_lt (n : Nat) (h : 3 ≤ n) : n.choose (n/2) < catalan n := by
  induction n,h using Nat.le_induction with
  | base => rw [catalan_three]; decide
  | succ n hn ih =>
    have m := middle_growth n
    have c := catalan_growth n (by omega)
    omega

/-- Closed-form color-witness bound for any graph order and any d ≥ 3 movable
points. The number of colors tested is the d-th Catalan number minus one. -/
theorem catalan_palette_graph {n k d : Nat} (hd : 3 ≤ d) (g : Coloring n k)
    (w : Lines n) (u v : Fin d → Fin n) :
    (∃ p : Perm (Fin d),Works g (draw w u v p)) ↔
    ∀ S : Finset (Fin k),S.card ≤ ((2*d).choose d / (d+1))-1 → ∃ p : Perm (Fin d),
      ∀ c∈S,Connected (Joined g (draw w u v p) c) := by
  have cat : catalan d=(2*d).choose d/(d+1) := catalan_eq_centralBinom_div d
  have le : paletteSize d ≤ catalan d-1 := max_le (Nat.sub_le_sub_right (Records.count_le_catalan d) 1)
    (by have h := middle_lt d hd; omega)
  rw [←cat]
  refine ⟨fun ⟨p,ok⟩ _ _ => ⟨p,fun c _ => ok c⟩,?_⟩
  exact fun localRepairs => (slot_palette_graph d g w u v).mpr (fun S hs => localRepairs S (hs.trans le))

#print axioms catalan_palette_graph
end WildSlots
