import ShortCredit42
import LongCredit
namespace WildSieve.FortyTwo
open Finset WildExact EvenTriples
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
local instance (priority := 2000) exactVertexEq {m : Nat} : DecidableEq (Fin m) := (inferInstance : LinearOrder (Fin m)).toDecidableEq

private noncomputable def losses (F : Factor V C) (j : Nat) :=
  (cuts F (Fin.last 41) 14 j).biUnion (fun S => noSix F univ∩hit S)

private theorem loss_mem (F : Factor V C) (j : Nat) {S : Finset V} {L : Layout (univ : Finset V)}
    (hs : S∈cuts F (Fin.last 41) 14 j) (la : L∈noSix F univ) (lost : L∈hit S) :
    L∈losses F j := by
  classical
  unfold losses
  exact mem_biUnion.mpr ⟨S,hs,mem_inter.mpr ⟨la,lost⟩⟩

private def longMass (j : Nat) := pureTotal 42 14 j*(ways j-saving false (3*j/2) j)*
  (ways (14-j)-saving false (3*(14-j)/2) (14-j))

private theorem late_bound (F : Factor V C) (j : Nat) (range : j=4 ∨ j=6) :
    (losses F j).card≤longMass j := by
  classical
  let H := cuts F (Fin.last 41) 14 j
  let p := (ways j-saving false (3*j/2) j)*(ways (14-j)-saving false (3*(14-j)/2) (14-j))
  have per (S) (h : S∈H) : (noSix F univ∩hit S).card≤p := by
    obtain ⟨c,hc⟩ := side_mem.mp h
    obtain ⟨_,sz,cl⟩ := candidate_mem.mp hc
    exact long_noSix F S c (by simpa using cl) j (14-j) sz
      (by rw [card_compl,Fintype.card_fin,sz];omega) (by omega) (by omega)
  have total := card_biUnion_le.trans (sum_le_sum (s:=H) per)
  rw [sum_const,nsmul_eq_mul] at total
  have high := pure_global F (Fin.last 41) 14 j 42 (by simp) (by simp)
  exact total.trans (by simpa [longMass,p,Nat.mul_assoc] using Nat.mul_le_mul_right p high)

attribute [irreducible] losses

private theorem survive_two {α : Type} [DecidableEq α] (A B C : Finset α) (less : (B∪C).card<A.card) :
    ∃ x∈A,x∉B ∧ x∉C := by
  classical
  by_contra! none
  apply (Nat.not_le_of_gt less)
  apply card_le_card
  intro x hx
  by_cases b : x∈B
  · exact mem_union_left _ b
  · exact mem_union_right _ (none x hx b)

/-- Every proper 41-coloring of K42 admits a winning partition into
fourteen triples. The graph has wild number 28. -/
theorem exact_K42 (g : Coloring 42 41) : Exact g 28 := by
  classical
  let F : Factor V C := coloringFactor g
  let A : Finset (Layout (univ : Finset V)) := noSix F univ
  let B : Finset (Layout (univ : Finset V)) := (marks F univ).biUnion hit
  have eq : A=Bᶜ := by
    ext D
    simp only [A,B,noSix_mem,mem_compl,mem_biUnion,not_exists,not_and,hit]
  have deck : A.card+B.card=ways 14 := by
    rw [eq,card_compl,card_layout 14 (univ:Finset V) (by simp)]
    have h := B.card_le_univ
    rw [card_layout 14 (univ:Finset V) (by simp)] at h
    omega
  have s := short_budget F
  change 1000*B.card≤723*ways 14 at s
  have l4 := late_bound F 4 (Or.inl rfl)
  have l6 := late_bound F 6 (Or.inr rfl)
  have price : 1000*(longMass 4+longMass 6)<277*ways 14 := by decide
  have covered : (losses F 4∪losses F 6).card<A.card := by
    have both := (card_union_le (losses F 4) (losses F 6)).trans (Nat.add_le_add l4 l6)
    omega
  obtain ⟨L,la,miss4,miss6⟩ := survive_two A (losses F 4) (losses F 6) covered
  have pass (j) (hj : j∈shortLevels∪longLevels 14) (S) (hs : S∈cuts F (Fin.last 41) 14 j) :
      L∉sealEvent S := by
    intro fail
    have lost : L∈hit S := local_seal_mem.mpr (mem_seal.mp fail)
    obtain ⟨c,hc⟩ := side_mem.mp hs
    obtain ⟨_,sz,cl⟩ := candidate_mem.mp hc
    have closed : Closed (F.f c) S := by simpa using cl
    have parity := closed_size (F.invol c) (F.moving c) closed
    have max : 0<j ∧ j≤7 := by
      rcases mem_union.mp hj with h|h
      · simp [shortLevels] at h;omega
      · obtain ⟨ra,high⟩ := mem_filter.mp h
        have := mem_range.mp ra
        omega
    by_cases small : j=2
    · have six : S.card=6 := by omega
      exact noSix_mem.mp la S (mark_mem.mpr ⟨subset_univ _,six,c,closed⟩) lost
    have cut : L∈losses F j := loss_mem F j (S:=S) (L:=L) hs la lost
    rcases (show j=4 ∨ j=6 by omega) with e|e
    · exact miss4 (e ▸ cut)
    · exact miss6 (e ▸ cut)
  apply exact_of_upper (pure_upper g (Fin.last 41) 14 (by decide) L pass)
  intro w le works
  have lower := even_lower (by decide : 3≤41+1) g le works
  omega

#print axioms exact_K42
end WildSieve.FortyTwo
