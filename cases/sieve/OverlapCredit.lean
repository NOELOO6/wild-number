import LocalSeals
namespace WildSieve
open Finset

variable {I Ω : Type} [DecidableEq I] [DecidableEq Ω]

omit [DecidableEq I] in
/-- Count an incidence sum first by event, then by outcome. -/
private theorem tally (H : Finset I) (U : Finset Ω) (E : I → Finset Ω) (w : I → Ω → Nat) :
    (∑ i∈H,∑ x∈U∩E i,w i x)=∑ x∈U,∑ i∈H.filter (fun i => x∈E i),w i x := by
  classical
  simp_rw [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [←sum_filter]
  congr 1

/-- The degree of a hit counts only other hits from a selected neighborhood.
The third-order correction can ignore every pair outside this neighborhood. -/
theorem overlap_credit (H : Finset I) (E : I → Finset Ω) (N : I → Finset I)
    (adj : ∀ i∈H,N i⊆H.erase i) :
    6*(H.biUnion E).card+3*(∑ i∈H,∑ j∈N i,(E i∩E j).card) ≤
      6*(∑ i∈H,(E i).card)+
      ∑ i∈H,∑ j∈N i,∑ k∈(N i).erase j,(E i∩E j∩E k).card := by
  classical
  let U := H.biUnion E
  let hit (x : Ω) := H.filter (fun i => x∈E i)
  let D (i : I) (x : Ω) := ((N i).filter (fun j => x∈E j)).card
  have keep (i) (h : i∈H) : U∩E i=E i :=
    inter_eq_right.mpr (fun x hx => mem_biUnion.mpr ⟨i,h,hx⟩)
  have allTally (w : I → Ω → Nat) : (∑ i∈H,∑ x∈E i,w i x)=∑ x∈U,∑ i∈hit x,w i x := by
    rw [←tally H U E w]
    exact sum_congr rfl (fun i hi => by rw [keep i hi])
  have first : (∑ i∈H,(E i).card)=∑ x∈U,(hit x).card := by
    simpa [sum_const,nsmul_eq_mul,keep,hit] using allTally (fun _ _ => 1)
  have pair (i) : (∑ j∈N i,(E i∩E j).card)=∑ x∈E i,D i x := by
    simpa [D] using tally (N i) (E i) E (fun _ _ => 1)
  have second : (∑ i∈H,∑ j∈N i,(E i∩E j).card)=∑ x∈U,∑ i∈hit x,D i x := by
    simp_rw [pair]
    simpa [keep,hit] using allTally D
  have triple (i) : (∑ j∈N i,∑ k∈(N i).erase j,(E i∩E j∩E k).card)=
      ∑ x∈E i,D i x*(D i x-1) := by
    have row (j) : (∑ k∈(N i).erase j,(E i∩E j∩E k).card)=
        ∑ x∈E i∩E j,(((N i).erase j).filter (fun k => x∈E k)).card := by
      simpa using tally ((N i).erase j) (E i∩E j) E (fun _ _ => 1)
    simp_rw [row]
    rw [tally (N i) (E i) E (fun j x => (((N i).erase j).filter (fun k => x∈E k)).card)]
    apply sum_congr rfl
    intro x _
    let L := (N i).filter (fun k => x∈E k)
    have size (j) (hj : j∈L) : (((N i).erase j).filter (fun k => x∈E k)).card=D i x-1 := by
      have eq : ((N i).erase j).filter (fun k => x∈E k)=L.erase j := by ext k; simp [L,and_assoc,and_left_comm]
      rw [eq,card_erase_of_mem hj]
    rw [sum_congr rfl size,sum_const]
    simp [D,L,nsmul_eq_mul]
  have third : (∑ i∈H,∑ j∈N i,∑ k∈(N i).erase j,(E i∩E j∩E k).card)=
      ∑ x∈U,∑ i∈hit x,D i x*(D i x-1) := by
    simp_rw [triple]
    simpa [keep,hit] using allTally (fun i x => D i x*(D i x-1))
  have point (x) (hx : x∈U) : 6+3*(∑ i∈hit x,D i x) ≤
      6*(hit x).card + ∑ i∈hit x,D i x*(D i x-1) := by
    obtain ⟨j,jh,xj⟩ := mem_biUnion.mp hx
    have pos := card_pos.mpr (show (hit x).Nonempty from ⟨j,mem_filter.mpr ⟨jh,xj⟩⟩)
    let z := if (hit x).card=1 then 6 else if (hit x).card=2 then 3 else 2
    have need : 6≤(hit x).card*z := by
      dsimp [z];split <;> rename_i h
      · rw [h]
      · split <;> rename_i h'
        · rw [h']
        · omega
    have per (i) (hi : i∈hit x) : z+3*D i x≤6+D i x*(D i x-1) := by
      have sub : (N i).filter (fun k => x∈E k)⊆(hit x).erase i := by
        intro k hk
        have a := mem_erase.mp (adj i (mem_filter.mp hi).1 (mem_filter.mp hk).1)
        exact mem_erase.mpr ⟨a.1,mem_filter.mpr ⟨a.2,(mem_filter.mp hk).2⟩⟩
      have bound := card_le_card sub
      rw [card_erase_of_mem hi] at bound
      change D i x≤(hit x).card-1 at bound
      by_cases large : 4≤D i x
      · have prod := Nat.mul_le_mul_left (D i x) (show 3≤D i x-1 by omega)
        have zv : z≤6 := by dsimp [z];split <;> (first | decide | split <;> decide)
        omega
      · rcases (show D i x=0 ∨ D i x=1 ∨ D i x=2 ∨ D i x=3 by omega) with e|e|e|e <;>
          rw [e] <;> dsimp [z] <;> split <;> (first | omega | split <;> omega)
    have total := sum_le_sum per
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,←mul_sum] at total
    omega
  have all := sum_le_sum (s:=U) point
  rw [first,second,third]
  simpa [sum_add_distrib,←mul_sum,nsmul_eq_mul,Nat.mul_comm,U] using all
end WildSieve
