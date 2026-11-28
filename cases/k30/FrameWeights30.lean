import ProfileBills30
import RegionLayouts

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) weightEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 10000

def occupancy (Q : Finset V) (z : V → Fin 4) (i : Fin 4) := (Q∩zone z i).card

theorem occupancy_count (Q : Finset V) (z : V → Fin 4) (i : Fin 4) :
    (Q.val.map z).count i=occupancy Q z i := by
  rw [Multiset.count_map]
  change (Q.filter (fun x => i=z x)).card=_
  unfold occupancy
  congr 1
  ext v
  simp [zone,eq_comm]

theorem selected_count (Q : Finset V) (z : V → Fin 4) (p : Fin 4 → Bool) :
    (Q∩selected z p).card=∑ i,if p i then occupancy Q z i else 0 := by
  have one (i : Fin 4) : occupancy Q z i=(Q.filter (fun x => z x=i)).card := by
    unfold occupancy
    congr 1
    ext v; simp [zone]
  have group := sum_card_fiberwise_eq_card_filter Q (univ.filter fun i => p i) z
  rw [←sum_filter]
  simp_rw [one]
  rw [group]
  congr 1
  ext v
  simp [selected]

theorem occupancy_total (Q : Finset V) (z : V → Fin 4) :
    occupancy Q z 0+occupancy Q z 1+occupancy Q z 2+occupancy Q z 3=Q.card := by
  have h := selected_count Q z (fun _ => true)
  simpa [selected,Fin.sum_univ_four] using h.symm

private theorem right_count (Q : Finset V) (z : V → Fin 4) (t : Fin 3) :
    (Q \ selected z (leftMask t)).card=
      (if t.val=2 then occupancy Q z 0 else 0)+(if t.val=0 then 0 else occupancy Q z 1)+occupancy Q z 3 := by
  have comp : Q \ selected z (leftMask t)=Q∩selected z (fun i => !(leftMask t i)) := by
    ext v
    simp [selected]
  rw [comp,selected_count,Fin.sum_univ_four]
  have masks : ∀ j : Fin 3,(!leftMask j 0)=decide (j.val=2) ∧
      (!leftMask j 1)=decide (j.val≠0) ∧ (!leftMask j 2)=false ∧ (!leftMask j 3)=true := by decide
  obtain ⟨a,b,l,r⟩ := masks t
  rw [a,b,l,r]
  by_cases h : t.val=0 <;> simp [h]

theorem mark_size (z : V → Fin 4) (t : Fin 3) (sizes : ∀ i,(zone z i).card=zoneSize t i) :
    (selected z hitMask).card=6 := by
  have h := selected_count univ z hitMask
  simpa [occupancy,Fin.sum_univ_four,hitMask,sizes,zoneSize] using h

private theorem marked_iff (Q : Finset V) (six : Q.card=6) (z : V → Fin 4) (t : Fin 3)
    (sizes : ∀ i,(zone z i).card=zoneSize t i) :
    Q≠selected z hitMask ↔ occupancy Q z 0+occupancy Q z 1<6 := by
  have h := selected_count Q z hitMask
  rw [Fin.sum_univ_four,show hitMask 0=true by decide,show hitMask 1=true by decide,show hitMask 2=false by decide,show hitMask 3=false by decide] at h
  simp only [Bool.false_eq_true,if_false,if_true,add_zero] at h
  have cap := card_le_card (inter_subset_left : Q∩selected z hitMask⊆Q)
  have sz := mark_size z t sizes
  constructor
  · intro ne
    by_contra! full
    have s : (Q∩selected z hitMask).card=6 := by omega
    have a := eq_of_subset_of_card_le (inter_subset_left : Q∩selected z hitMask⊆Q) (by omega)
    have b := eq_of_subset_of_card_le (inter_subset_right : Q∩selected z hitMask⊆selected z hitMask) (by omega)
    exact ne (a.symm.trans b)
  · rintro strict eq
    have same : (Q∩selected z hitMask).card=6 := by rw [eq,inter_self,sz]
    omega

theorem frame_size (z : V → Fin 4) (t : Fin 3) (sizes : ∀ i,(zone z i).card=zoneSize t i) :
    (Regions.decks z).card=otherDenom t := by
  rw [Regions.decks_card]
  change (∏ i,layoutWays (zone z i).card)=_
  simp only [Fin.prod_univ_four,sizes,zoneSize,Fin.val_zero,Fin.reduceFinMk,otherDenom,show layoutWays 3=1 by decide,one_mul]

private theorem tiny (a : Nat) (le : a≤3) :
    sealWays 3 a=if a%3=0 then 1 else 0 := by
  have full : ∀ i : Fin 4,sealWays 3 i.val=if i.val%3=0 then 1 else 0 := by decide
  exact full ⟨a,by omega⟩

theorem frame_other_weight (Q : Finset V) (six : Q.card=6) (z : V → Fin 4) (t k : Fin 3)
    (sizes : ∀ i,(zone z i).card=zoneSize t i) :
    (if Q≠selected z hitMask ∧ (Q∩selected z (leftMask t)).card=6-3*k.val then
      (Regions.decks z∩localSeal univ Q).card else 0)=otherCompletions t k (Q.val.map z) := by
  have small (j : Fin 4) : occupancy Q z j≤zoneSize t j := (card_le_card inter_subset_right).trans_eq (sizes j)
  have eq : (Q∩selected z (leftMask t)).card=6-3*k.val ↔
      (if t.val=2 then occupancy Q z 0 else 0)+(if t.val=0 then 0 else occupancy Q z 1)+occupancy Q z 3=3*k.val := by
    have h := card_sdiff_add_card_inter Q (selected z (leftMask t))
    rw [right_count,six] at h
    have := k.isLt
    omega
  simp only [marked_iff Q six z t sizes,eq,Regions.decks_seal_card]
  change (if _ then ∏ i, sealWays (zone z i).card (occupancy Q z i) else 0)=_
  simp only [Fin.prod_univ_four,sizes,zoneSize,Fin.val_zero,Fin.reduceFinMk,otherCompletions,occupancy_count]
  rw [tiny _ (small 0),tiny _ (small 1)]
  split_ifs <;> simp_all

end WildSieve.Thirty.Graph
