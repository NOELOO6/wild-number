import TripleNeighbors
import JointDegrees

namespace WildSieve.SixCounts
open Finset
variable {n k : Nat}
local notation "V" => Fin n
local notation "C" => Fin k
local instance (priority := 2000) restrictedEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

/-- A fixed triple can be joined to at most u + 3⌊u/2⌋ triples in a region
of size u. Each color without an internal edge must send a chosen vertex
into the region. The three internal edges account for the other colors. -/
theorem restricted_neighbors (F : Factor V C) (A U : Finset V) (a : A.card=3) :
    ((neighbors F A).filter (fun B => B⊆U)).card≤U.card+3*(U.card/2) := by
  classical
  obtain ⟨z,za⟩ := card_pos.mp (by omega : 0<A.card)
  let N (c : C) := (colorNeighbors F A c).filter (fun B => B⊆U)
  have lift : (neighbors F A).filter (fun B => B⊆U) ⊆ (univ : Finset C).biUnion N := by
    intro B hb
    obtain ⟨p,sub⟩ := mem_filter.mp hb
    obtain ⟨c,_,hc⟩ := mem_biUnion.mp p
    exact mem_biUnion.mpr ⟨c,mem_univ _,mem_filter.mpr ⟨hc,sub⟩⟩
  have each (c : C) : (N c).card ≤ (if c∈into F z U then 1 else 0)+(U.card/2)*Inside F c A := by
    let R := SixCounts.forcedOut F A c
    have bound := count_free (F.invol c) (F.moving c) U R (N c) 3 (fun B h => by
      obtain ⟨old,sub⟩ := mem_filter.mp h
      obtain ⟨_,size,fit,cl⟩ := SixCounts.strip old
      exact ⟨sub,size,fit,cl⟩)
    have sz := SixCounts.forced_size F A a c
    change R.card=_ at sz
    have one := SixCounts.inside_le_one F A a c
    rcases (show Inside F c A=0 ∨ Inside F c A=1 by omega) with zero|two
    · rw [zero] at sz ⊢
      have zOut : F.f c z∉A := by
        intro inside
        have nonempty : (paired (F.f c) A).Nonempty := ⟨z,mem_filter.mpr ⟨za,inside⟩⟩
        have pos := card_pos.mpr nonempty
        rw [paired_size (F.invol c) (F.moving c)] at pos
        change 0<2*Inside F c A at pos
        omega
      have forced : F.f c z∈R := mem_sdiff.mpr ⟨mem_image.mpr ⟨z,za,rfl⟩,zOut⟩
      by_cases yes : c∈into F z U
      · simp [yes,sz] at bound ⊢
        exact bound
      · have empty : N c=∅ := eq_empty_iff_forall_not_mem.mpr (fun B hb => by
          obtain ⟨hc,sub⟩ := mem_filter.mp hb
          exact yes ((into_mem F z U c).mpr (sub ((SixCounts.strip hc).2.2.1 forced))))
        simp [empty]
    · rw [two] at sz ⊢
      have cap := ends_bound (F.invol c) (U \ R)
      have region := card_le_card (sdiff_subset : U \ R ⊆ U)
      simp [sz] at bound
      omega
  have all := (card_le_card lift).trans (card_biUnion_le.trans (sum_le_sum (s:=univ) (fun c _ => each c)))
  rw [sum_add_distrib,←mul_sum,sum_inside,a] at all
  have count : (∑ c : C,if c∈into F z U then 1 else 0)=(into F z U).card := by simp
  rw [count,into_size] at all
  change (neighbors F A |>.filter (fun B => B⊆U)).card ≤ (U.erase z).card+(U.card/2)*3 at all
  have cap := card_le_card (erase_subset z U)
  omega

end WildSieve.SixCounts
