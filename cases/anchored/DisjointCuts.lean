import CutSelection
import ThreeLabels
import Anchor30

namespace WildAnchor.K30
open Finset WildExact
set_option maxRecDepth 12000

abbrev Groups := Finset (Fin 10)
abbrev Side := Sides 10 (tag root)

def groupMask (a : Fin 1024) : Groups := univ.filter fun i => a.val.testBit i.val
def twos : Finset (Fin 1024) := univ.filter fun a => (groupMask a).card=2
def cuts22 : Finset (Fin 1024 × Fin 1024) := (twos ×ˢ twos).filter fun q =>
  q.1<q.2 ∧ q.1.val &&& q.2.val=0
abbrev DoubleCut := ↥cuts22

def left (q : DoubleCut) := groupMask q.val.1
def right (q : DoubleCut) := groupMask q.val.2
def normalize (A : Groups) := if tag root∈A then Aᶜ else A

private theorem shapes : ∀ q : DoubleCut,
    (normalize (left q)).Nonempty ∧ tag root∉normalize (left q) ∧
    (normalize (left q∪right q)).Nonempty ∧ tag root∉normalize (left q∪right q) := by native_decide

def smaller (q : DoubleCut) : Side := ⟨normalize (left q),(shapes q).1,(shapes q).2.1⟩
def larger (q : DoubleCut) : Side :=
  ⟨normalize (left q∪right q),(shapes q).2.2.1,(shapes q).2.2.2⟩

private theorem distinct_sizes : ∀ p q : DoubleCut, smaller p ≠ larger q := by native_decide

/-- Two different divisions of the same four groups into pairs intersect
in a single group on at least one choice of sides. -/
private theorem collision : ∀ p q : DoubleCut, p≠q → larger p=larger q →
    ∃ A∈[left p,right p], ∃ B∈[left q,right q], ∃ x : Fin 10, A∩B={x} := by native_decide

def placed (p : Shuffle (Fin 15)) (i : Fin 15) (b : Bool) := tag ((perm p).symm (i,b))

def ClosedBy (p : Shuffle (Fin 15)) (next : Equiv.Perm (Fin 15)) (A : Groups) :=
  ∀ i,placed p i false∈A ↔ placed p (next i) true∈A

private theorem normal_closed {p next A} (h : ClosedBy p next A) : ClosedBy p next (normalize A) := by
  intro i
  unfold normalize
  split
  · simpa using not_congr (h i)
  · exact h i

private theorem two_closed {p next A B} (a : ClosedBy p next A) (b : ClosedBy p next B) :
    ClosedBy p next (A∪B) ∧ ClosedBy p next (A∩B) := by
  constructor <;> intro i
  · simpa only [mem_union] using or_congr (a i) (b i)
  · simpa only [mem_inter] using and_congr (a i) (b i)

private theorem triples : ∀ x : Fin 10, (univ.filter (fun y : Point 15 => tag y=x)).card=3 := by
  native_decide

private theorem singleton_open (p : Shuffle (Fin 15)) (next : Equiv.Perm (Fin 15)) (x : Fin 10) :
    ¬ClosedBy p next {x} := by
  classical
  intro cl
  let yes (z : Point 15) := if tag z=x then (1 : Nat) else 0
  have total : (∑ z,yes z)=3 := by simpa [yes,sum_boole] using triples x
  have ren : (∑ z,yes ((perm p).symm z))=∑ z,yes z :=
    Fintype.sum_equiv (perm p).symm _ _ (fun _ => rfl)
  have cut (i : Fin 15) : yes ((perm p).symm (i,false))=yes ((perm p).symm (next i,true)) := by
    have eq : placed p i false=x ↔ placed p (next i) true=x := by simpa using cl i
    change (if placed p i false=x then _ else _)=(if placed p (next i) true=x then _ else _)
    simp only [eq]
  have rotate : (∑ i,yes ((perm p).symm (next i,true)))=∑ i,yes ((perm p).symm (i,true)) :=
    Fintype.sum_equiv next _ _ (fun _ => rfl)
  rw [Fintype.sum_prod_type] at ren
  simp only [Fintype.sum_bool,Finset.sum_add_distrib] at ren
  have equal : (∑ i,yes ((perm p).symm (i,false)))=∑ i,yes ((perm p).symm (i,true)) :=
    (sum_congr rfl (fun i _ => cut i)).trans rotate
  omega

def both (p : Shuffle (Fin 15)) (next : Equiv.Perm (Fin 15)) (q : DoubleCut) :=
  ClosedBy p next (left q) ∧ ClosedBy p next (right q)

private theorem no_collision {p next} {u v : DoubleCut} (a : both p next u)
    (b : both p next v) (eq : larger u=larger v) : u=v := by
  by_contra ne
  obtain ⟨A,ha,B,hb,x,hx⟩ := collision _ _ ne eq
  have closed {q : DoubleCut} (h : both p next q) {S} (s : S∈[left q,right q]) :
      ClosedBy p next S := by
    rcases (show S=left q ∨ S=right q by simpa using s) with rfl|rfl
    · exact h.1
    · exact h.2
  exact singleton_open p next x (hx ▸ (two_closed (closed a ha) (closed b hb)).2)

theorem closed_iff (p : Shuffle (Fin 15)) (next : Equiv.Perm (Fin 15)) (a : Side) :
    ClosedBy p next a.val ↔ ∃ b : Mask 15,Fits p (groupSide tag a) (row next (bits b)) := by
  constructor
  · intro cl
    let f (i : Fin 15) := decide (placed p i false∈a.val)
    obtain ⟨b,hb⟩ := all_bits f
    refine ⟨b,(fits_iff ..).mpr ?_⟩
    intro y
    obtain ⟨⟨i,z⟩,rfl⟩ := (perm p).symm.surjective y
    simp only [Equiv.apply_symm_apply,groupSide,flag_state]
    cases z
    · simp [flag,row,hb,f,placed]
    · change decide (placed p i true ∈ a.val)=bits b (next.symm i)
      rw [hb]
      apply Bool.eq_iff_iff.mpr
      simp only [f,decide_eq_true_eq]
      simpa using (cl (next.symm i)).symm
  · rintro ⟨b,fit⟩ i
    have atPoint (v : Fin 15) (z : Bool) := (fits_iff ..).mp fit ((perm p).symm (v,z))
    have h := atPoint i false
    have k := atPoint (next i) true
    simp only [groupSide,flag_state,Equiv.apply_symm_apply] at h k
    change decide (placed p i false∈a.val)=bits b i at h
    change decide (placed p (next i) true∈a.val)=bits b (next.symm (next i)) at k
    rw [Equiv.symm_apply_apply] at k
    simpa only [decide_eq_true_eq] using Bool.eq_iff_iff.mp (h.trans k.symm)

noncomputable def doubles (p : Shuffle (Fin 15)) (next : Equiv.Perm (Fin 15)) : Finset DoubleCut := by
  classical exact univ.filter (both p next)

noncomputable def closedSides (p : Shuffle (Fin 15)) (next : Equiv.Perm (Fin 15)) : Finset Side := by
  classical exact univ.filter fun a : Side => ClosedBy p next a.val

theorem row_credit (p : Shuffle (Fin 15)) (next : Equiv.Perm (Fin 15)) :
    (if (closedSides p next).Nonempty then 1 else 0)+(doubles p next).card ≤
      (closedSides p next).card := by
  classical
  let H := closedSides p next
  change (if H.Nonempty then 1 else 0)+(doubles p next).card≤H.card
  have included (u : DoubleCut) (hu : u∈doubles p next) : larger u∈H :=
    mem_filter.mpr ⟨mem_univ _,normal_closed (two_closed ((mem_filter.mp hu).2).1 ((mem_filter.mp hu).2).2).1⟩
  let D := doubles p next
  have sub : D.image larger ⊆ H := by
    rintro x hx; obtain ⟨q,hq,rfl⟩ := mem_image.mp hx; exact included q hq
  have size : (D.image larger).card=D.card := card_image_of_injOn (by
    intro u hu v hv e
    exact no_collision (mem_filter.mp hu).2 (mem_filter.mp hv).2 e)
  by_cases occ : D.Nonempty
  · obtain ⟨u,hu⟩ := occ
    have inside : smaller u∈H := mem_filter.mpr ⟨mem_univ _,normal_closed ((mem_filter.mp hu).2).1⟩
    have out : smaller u∉D.image larger := by
      rintro h; obtain ⟨v,_,eq⟩ := mem_image.mp h; exact distinct_sizes _ _ eq.symm
    have strict : D.image larger ⊂ H := Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun e => out (e ▸ inside)⟩
    have h := card_lt_card strict
    rw [size] at h
    rw [if_pos ⟨_,inside⟩]
    exact (Nat.one_add D.card).symm ▸ Nat.succ_le_of_lt h
  · have zero : (doubles p next).card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp occ)
    split <;> simp_all [card_pos]

end WildAnchor.K30
