import TripleIncidence
import PatternGeometry
import OverlapCredit

namespace WildSieve.TripleIncidence
open Finset
variable {n : Nat}
local notation "V" => Fin n
local instance (priority := 2000) densityEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

/-- Unordered triple partitions containing none of the specified triples. -/
noncomputable def clear (H : Finset (Finset V)) : Finset (Layout (univ : Finset V)) := by
  classical exact univ.filter (fun D => ∀ A∈H,A∉D.val)

private noncomputable abbrev E (A : Finset V) := SixCounts.event ({A} : Blocks V)

private theorem present {A : Finset V} {D : Layout (univ : Finset V)} : D∈E A ↔ A∈D.val := by
  classical simp [E,SixCounts.event,extensions]

private theorem joint {t : Nat} (order : n=3*t) {A B : Finset V}
    (sa : A.card=3) (sb : B.card=3) (ab : Disjoint A B) :
    (E A∩E B).card=ways (t-2) := by
  have ne : A≠B := by rintro rfl; have e := disjoint_self.mp ab; simp [e] at sa
  have ok := (singleton_triple sa).combine (singleton_triple sb) (by simpa using ab)
  rw [E,E,SixCounts.event_union,SixCounts.event_mass t order ok]
  rw [card_union_of_disjoint (by simpa using ne.symm),card_singleton,card_singleton]

private theorem three {t : Nat} (order : n=3*t) {A B C : Finset V}
    (sa : A.card=3) (sb : B.card=3) (sc : C.card=3)
    (ab : Disjoint A B) (ac : Disjoint A C) (cb : C≠B) :
    (E A∩E B∩E C).card=if Disjoint B C then ways (t-3) else 0 := by
  classical
  split
  next bc =>
    have ne {X Y : Finset V} (sx : X.card=3) (dis : Disjoint X Y) : X≠Y := by
      rintro rfl; have e := disjoint_self.mp dis; simp [e] at sx
    have ok := (singleton_triple sa).combine (singleton_triple sb) (by simpa using ab)
    have all := ok.combine (singleton_triple sc) (by simpa using And.intro ac bc)
    rw [E,E,E,SixCounts.event_union,SixCounts.event_union,SixCounts.event_mass t order all]
    rw [card_union_of_disjoint (by simp [(ne sa ac).symm,cb]),
      card_union_of_disjoint (by simpa using (ne sa ab).symm),card_singleton,card_singleton,card_singleton]
  next bc =>
    apply card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr ?_)
    intro D hd
    exact bc (D.property.1.separate _ (present.mp (mem_inter.mp (mem_inter.mp hd).1).2)
      _ (present.mp (mem_inter.mp hd).2) cb.symm)

/-- A third-order bound for all forbidden triples of bounded pair degree.
The ordered disjoint-pair count keeps the same coefficient on both sides. -/
theorem density_budget (t k : Nat) (order : n=3*t) (H : Finset (Finset V))
    (size : ∀ A∈H,A.card=3) (cap : PairBound H k) :
    ∃ p : Nat,
      H.card*(H.card+2)≤p+H.card*(3*(k*(n-1)/2)) ∧
      6*(ways t)+p*(3*ways (t-2))≤6*(clear H).card+
        6*(H.card*ways (t-1))+p*((k*(n-6).choose 2/3)*ways (t-3)) := by
  classical
  let N (T : Finset V) := within H Tᶜ
  let P := ∑ T∈H,(N T).card
  have info {A T : Finset V} (h : A∈N T) : A∈H ∧ Disjoint T A :=
    ⟨(mem_filter.mp h).1,disjoint_left.mpr (fun _ tx ax => mem_compl.mp ((mem_filter.mp h).2 ax) tx)⟩
  have adj (T) (ht : T∈H) : N T⊆H.erase T := by
    intro A ha
    obtain ⟨base,dis⟩ := info ha
    refine mem_erase.mpr ⟨?_,base⟩
    rintro rfl
    have e := disjoint_self.mp dis
    have s := size A ht
    simp [e] at s
  have low := sum_le_sum (s:=H) (fun T h => disjoint_lower H size k cap h)
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] at low
  refine ⟨P,by simpa only [Nat.mul_add] using low,?_⟩
  have u := overlap_credit H E N adj
  have one (T) (ht : T∈H) : (E T).card=ways (t-1) := by
    rw [E,SixCounts.event_mass t order (singleton_triple (size _ ht)),card_singleton]
  have two (T) (ht : T∈H) : (∑ A∈N T,(E T∩E A).card)=(N T).card*ways (t-2) := by
    rw [sum_congr rfl (fun A ha => joint order (size T ht) (size _ (info ha).1) (info ha).2),sum_const]
    rfl
  let cost := k*(n-6).choose 2/3*ways (t-3)
  have row (T) (ht : T∈H) (A) (ha : A∈N T) :
      (∑ B∈(N T).erase A,(E T∩E A∩E B).card)≤cost := by
    let R := (T∪A)ᶜ
    have ts := size T ht
    obtain ⟨base,dis⟩ := info ha
    have a := size A base
    have sz : R.card=n-6 := by rw [card_compl,Fintype.card_fin,card_union_of_disjoint dis,ts,a]
    have price := within_bound H size k cap R
    rw [sz] at price
    have fit : ((N T).erase A).filter (Disjoint A)⊆within H R := by
      intro B h
      obtain ⟨old,ab⟩ := mem_filter.mp h
      obtain ⟨bh,tb⟩ := info (mem_erase.mp old).2
      exact mem_filter.mpr ⟨bh,fun x hx => mem_compl.mpr (fun u => (mem_union.mp u).elim
        (fun v => disjoint_left.mp tb v hx) (fun v => disjoint_left.mp ab v hx))⟩
    have bound : (((N T).erase A).filter (Disjoint A)).card ≤ k*(n-6).choose 2/3 :=
      (card_le_card fit).trans (by omega)
    rw [sum_congr rfl (fun B h => three order ts a (size _ (info (mem_erase.mp h).2).1)
      dis (info (mem_erase.mp h).2).2 (mem_erase.mp h).1),←sum_filter,sum_const]
    exact Nat.mul_le_mul_right _ bound
  have third (T) (ht : T∈H) :
      (∑ A∈N T,∑ B∈(N T).erase A,(E T∩E A∩E B).card)≤(N T).card*cost := by
    simpa only [sum_const,nsmul_eq_mul,Nat.cast_id] using sum_le_sum (row T ht)
  have all := sum_le_sum third
  rw [←sum_mul] at all
  rw [sum_congr rfl one,sum_const,nsmul_eq_mul,sum_congr rfl two,←sum_mul] at u
  have eq : H.biUnion E=(clear H)ᶜ := by ext D; simp [clear,present]
  rw [eq,card_compl,card_layout t univ (by simpa using order)] at u
  have cw := (clear H).card_le_univ
  rw [card_layout t univ (by simpa using order)] at cw
  change _≤P*cost at all
  change 6*(ways t-(clear H).card)+3*(P*ways (t-2))≤_ at u
  rw [Nat.mul_left_comm 3 P] at u
  simp only [Nat.cast_id] at u
  dsimp [cost] at all
  omega

end WildSieve.TripleIncidence
