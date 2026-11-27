import AnchorPacking
namespace WildSieve.AnchorPacking
open Finset WildExact

local instance (priority := 2000) {m : Nat} : DecidableEq (Fin m) :=
  (inferInstance : LinearOrder (Fin m)).toDecidableEq
set_option maxRecDepth 10000

def anchor : Finset (Fin 16) := {0,1,2,15}
abbrev Outside := Free anchor

private def rows := (((include_str "layouts.txt").trim.splitOn "\n").map
  (fun line => (line.splitOn " ").map String.toNat!)).toArray

def decode (mask : Nat) : Finset Outside := univ.filter fun v => mask.testBit v.val.val

def cells (i : Fin 140) : Blocks Outside := ((rows[i.val]!).map decode).toFinset

private theorem cardRows : ∀ i : Fin 140,∀ b∈cells i,b.card=3 := by native_decide
private theorem apartRows : ∀ i : Fin 140,∀ a∈cells i,∀ b∈cells i,a≠b → ∀ v∈a,v∉b := by native_decide
private theorem fullRows : ∀ i : Fin 140,vertices (cells i)=univ := by native_decide

def drawing (i : Fin 140) : Layout (univ : Finset Outside) :=
  ⟨cells i,⟨cardRows i,fun a ha b hb ne => disjoint_left.mpr (fun v hv => apartRows i a ha b hb ne v hv)⟩,
    fullRows i⟩

def testedTriples : Finset (Finset Outside) := univ.biUnion cells

private theorem triple_load : ∀ T : Finset Outside,(∑ i : Fin 140,if T∈cells i then 1 else 0)≤6 := by native_decide
private theorem half_load : ∀ X : Finset Outside,(∑ i : Fin 140,if X∈halfSides (cells i) then 1 else 0)≤1 := by native_decide

/-- Seven of the listed triples may fail either anchor test. Every coloring
with those constraints admits a ten-edge layout. -/
theorem ten_from_packing (g : Coloring 15 15)
    (rain : Rainbow (coloringFactor (augment (by decide) g)) anchor)
    (few : (testedTriples∩badScopes (coloringFactor (augment (by decide) g)) anchor 15 3 4 1).card≤7) :
    Exact g 10 := by
  classical
  let F := coloringFactor (augment (by decide) g)
  let extra := testedTriples∩badScopes F anchor 15 3 4 1
  have hr : (15:Fin 16)∈anchor := by decide
  have bs : anchor.card=4 := by decide
  obtain ⟨i,p⟩ := anchor_wins F anchor 15 hr bs rain drawing (fun _ => 1) extra 6 1
    (fun i T mem bad => mem_inter.mpr ⟨mem_biUnion.mpr ⟨i,mem_univ _,mem⟩,bad⟩)
    (fun T _ => triple_load T) half_load (by
      have h : extra.card≤7 := few
      simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
      omega)
  apply exact_of_upper _ (fun _ => odd_lower (by decide) g)
  exact upper_from_layout g (by decide) anchor 3 4 hr bs (by decide) rain (Or.inr (by decide)) (drawing i) p

#print axioms ten_from_packing
end WildSieve.AnchorPacking
