import PlantedCuts
import StarDraw
import Rainbow
import Numeric
namespace WildSieve
local instance (priority := 2000) {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq
set_option maxHeartbeats 1000000
open Finset WildExact WildDeletion
variable {n : Nat}

private theorem matching_projection (g : Coloring n n) (odd : n%2=1) (c : Fin n) (w : Lines n) :
    ∃ q : Fin (n+1) → Fin n, (∀ x,q x.castSucc=x) ∧
      ∀ v,Walk (Joined g w c) (q v) (q (mate (augment odd g) c v)) := by
  let m := mate (augment odd g) c
  let root := Fin.last n
  have inv := mate_involutive (augment odd g) c
  have free (v) := (mate_spec (augment odd g) c v).1
  obtain ⟨p,hp⟩ := before_root (m root) (free root).symm
  let q : Fin (n+1) → Fin n := Fin.lastCases p id
  have qr : q root=p := Fin.lastCases_last
  have qo (x : Fin n) : q x.castSucc=x := Fin.lastCases_castSucc _
  refine ⟨q,qo,?_⟩
  intro v
  change Walk (Joined g w c) (q v) (q (m v))
  by_cases vr : v=root
  · rw [vr,qr,← hp,qo]
    exact .stay _
  obtain ⟨x,rfl⟩ := before_root v vr
  rw [qo]
  by_cases mr : m x.castSucc=root
  · have eq : m root=x.castSucc := (congrArg m mr).symm.trans (inv x.castSucc)
    have xp : p=x := Fin.castSucc_injective n (hp.trans eq)
    rw [mr,qr,xp]
    exact .stay _
  obtain ⟨y,hy⟩ := before_root _ mr
  rw [← hy,qo]
  apply Walk.step (E:=Joined g w c) (.stay x) (Or.inr ?_)
  have xy : x≠y := fun eq => free _ ((congrArg Fin.castSucc eq).trans hy)
  refine ⟨xy,?_⟩
  rw [← augment_paint odd g,hy]
  exact (mate_spec (augment odd g) c x.castSucc).2

/-- Realize the layout as ordinary wild lines. The added root has no wild
edge. In each color projection it is mapped to its unique matching partner. -/
theorem upper_from_layout (g : Coloring n n) (odd : n%2=1) (B : Finset (Fin (n+1))) (f t : Nat)
    (rb : Fin.last n∈B) (bs : B.card=f+1) (ws : Bᶜ.card=3*t)
    (rain : Rainbow (coloringFactor (augment odd g)) B) (shape : f=0 ∨ 3≤f)
    (L : Layout (univ : Finset (Free B)))
    (wins : ∀ j∈shortLevels ∪ longLevels t, ∀ X∈badScopes (coloringFactor (augment odd g)) B (Fin.last n) f t j,
      L∉sealEvent X) : Upper g (2*t+(f-1)) := by
  classical
  let root := Fin.last n
  let F := coloringFactor (augment odd g)
  let fixed := B.erase root
  let wild (T : Finset (Free B)) := spokes (oldPart (T.map (emb B)))
  let w := spokes (oldPart fixed) ∪ L.val.biUnion wild
  have out (T : Finset (Free B)) : root∉T.map (emb B) := by
    intro mr
    obtain ⟨a,_,eq⟩ := mem_map.mp mr
    have no : a.val∉B := by simpa only [Finset.mem_compl] using a.property
    change a.val=root at eq
    exact no (by rwa [eq])
  have size := L.property.1.card_vertices
  rw [L.property.2,card_univ,Fintype.card_coe] at size
  have cardfree := ws
  simp only [card_compl,Fintype.card_fin] at size cardfree
  have num : L.val.card=t := by omega
  refine ⟨w,?_,?_,?_⟩
  · intro e he
    rcases mem_union.mp he with i|i
    · exact spokes_legal _ _ i
    · obtain ⟨T,_,h⟩ := mem_biUnion.mp i
      exact spokes_legal _ _ h
  · have fixedCost : (spokes (oldPart fixed)).card ≤ f-1 := by
      apply (spokes_bound _).trans
      rw [old_size fixed (not_mem_erase _ _),card_erase_of_mem rb,bs]
      simp
    have freeCost : (L.val.biUnion wild).card ≤ 2*t := by
      apply card_biUnion_le.trans
      calc
        _ ≤ ∑ _ ∈ L.val,2 := sum_le_sum (fun T ht => by
          apply (spokes_bound _).trans
          rw [old_size _ (out T),card_map,L.property.1.size T ht])
        _ = _ := by simp [num,Nat.mul_comm]
    exact (card_union_le _ _).trans ((Nat.add_le_add fixedCost freeCost).trans_eq (Nat.add_comm _ _))
  intro c x y
  apply Classical.byContradiction
  intro lost
  obtain ⟨q,qo,colorPath⟩ := matching_projection g odd c w
  let S := univ.filter fun v => Walk (Joined g w c) x (q v)
  have inS (v : Fin (n+1)) : v∈S ↔ Walk (Joined g w c) x (q v) := by simp [S]
  have within (T : Finset (Fin (n+1))) (nr : root∉T) (draw : spokes (oldPart T)⊆w) : Cohesive T S := by
    intro a ha b hb sa
    obtain ⟨a,rfl⟩ := before_root a (fun ar => nr (by simpa only [root,ar] using ha))
    obtain ⟨b,rfl⟩ := before_root b (fun br => nr (by simpa only [root,br] using hb))
    have old := (inS _).mp sa
    apply (inS _).mpr
    apply old.join
    rw [qo,qo]
    exact Walk.mapInto (E:=Touch w) id (fun _ _ h => .step (.stay _) (Or.inl h))
      (in_star draw (old_mem.mpr ha) (old_mem.mpr hb))
  have sizeW : Bᶜ.card=3*t := ws
  apply no_cut F B root f t rb bs (by simpa only [Finset.card_compl,Fintype.card_fin] using sizeW) rain shape L wins c S
  · exact ⟨x.castSucc,(inS _).mpr (by rw [qo]; exact .stay _)⟩
  · exact ⟨y.castSucc,mem_compl.mpr (fun h => lost (by simpa only [qo] using (inS _).mp h))⟩
  · intro v sv
    exact (inS _).mpr (((inS _).mp sv).join (colorPath v))
  · exact within fixed (not_mem_erase _ _) subset_union_left
  · intro T ht
    exact within _ (out T) (fun e he => mem_union_right _ (mem_biUnion.mpr ⟨T,ht,he⟩))


end WildSieve
