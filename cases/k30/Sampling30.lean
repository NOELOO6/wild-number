import GraphBudget30
import SideSpectrum30

namespace WildSieve.Thirty.Graph
open Finset EvenTriples
set_option maxRecDepth 10000
set_option maxHeartbeats 1500000
local instance (priority := 2000) sampleEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq

noncomputable abbrev anchors (F : Factor V C) (c : C) := candidates F c ∅ univ 12

def sideWays := layoutWays 12 * layoutWays 18

theorem anchor_card (F : Factor V C) (c : C) : (anchors F c).card=5005 := by
  rw [anchors,show 12=2*6 by decide,candidate_pairs,full_pairs]
  decide

theorem seal_card (L : Finset V) (sz : L.card=12) : (localSeal univ L).card=sideWays := by
  rw [local_seal_ways _ _ (subset_univ _),card_univ,Fintype.card_fin,sz]
  rfl

noncomputable def anchorSum (F : Factor V C) (w : Finset V → ℚ) :=
  ∑ c,∑ L∈anchors F c,w L

noncomputable def localSum (L : Finset V) (w : Deck → ℚ) := ∑ D∈localSeal univ L,w D

noncomputable def cutAvg (F : Factor V C) (w : Finset V → ℚ) := anchorSum F w/(29*5005)
noncomputable def sideAvg (L : Finset V) (w : Deck → ℚ) := localSum L w/sideWays

noncomputable def sideHits (F : Factor V C) (L : Finset V) (D : Deck) (t : Fin 3) :=
  (marks F univ).filter fun Q => (Q∩L).card=6-3*t.val ∧ D∈localSeal univ Q

theorem anchor_const (F : Factor V C) (a : ℚ) : anchorSum F (fun _ => a)=29*5005*a := by
  simp [anchorSum,anchor_card,nsmul_eq_mul]
  ring

theorem sample_zero (F : Factor V C) (L : Finset V) (D : Deck) (hL : D∈localSeal univ L) :
    (∀ t,sideHits F L D t=∅) ↔ D∈noSix F univ := by
  classical
  constructor
  · intro ok
    apply noSix_mem.mpr
    intro Q mark seen
    have sz := (mark_mem.mp mark).2.1
    have cap := card_le_card (inter_subset_left : Q∩L⊆Q)
    have div := intersect_sealed seen hL
    have cat : ∃ t : Fin 3,(Q∩L).card=6-3*t.val := by
      rcases (show (Q∩L).card=6 ∨ (Q∩L).card=3 ∨ (Q∩L).card=0 by omega) with h|h|h
      · exact ⟨0,h⟩
      · exact ⟨1,h⟩
      · exact ⟨2,h⟩
    obtain ⟨t,ht⟩ := cat
    have mem : Q∈sideHits F L D t := mem_filter.mpr ⟨mark,ht,seen⟩
    rw [ok] at mem
    simp at mem
  · intro h t
    apply eq_empty_iff_forall_not_mem.mpr
    intro Q inHits
    obtain ⟨mark,_,seen⟩ := mem_filter.mp inHits
    exact noSix_mem.mp h Q mark seen

attribute [local irreducible] localSeal noSix candidates lateBad

/-- A surviving twelve-point failure contributes at least once to the
experiment that chooses a color, a closed twelve-set and a split layout. -/
theorem late_le_sample (F : Factor V C) :
    ((lateBad F).card : ℚ) ≤ anchorSum F (fun L => ((noSix F univ∩localSeal univ L).card : ℚ)) := by
  classical
  let E (L : Finset V) := noSix F univ∩localSeal univ L
  have covers : cuts F (Fin.last 29) 10 4 = (univ : Finset C).biUnion (anchors F) := by
    change sides F ∅ univ 12 = _
    ext L
    simp only [side_mem,mem_biUnion,mem_univ,true_and,anchors]
  have bound : (lateBad F).card ≤ ∑ c,∑ L∈anchors F c,(E L).card := by
    unfold lateBad
    rw [covers,biUnion_biUnion]
    exact card_biUnion_le.trans (sum_le_sum (fun _ _ => card_biUnion_le))
  change ((lateBad F).card : ℚ) ≤ ∑ c,∑ L∈anchors F c,((E L).card : ℚ)
  exact_mod_cast bound

noncomputable def noHitChance (F : Factor V C) :=
  cutAvg F (fun L => ((noSix F univ∩localSeal univ L).card : ℚ)/sideWays)

theorem late_fraction (F : Factor V C) :
    ((lateBad F).card : ℚ)/(ways 10 : ℚ)≤longMass*noHitChance F := by
  have eq : noHitChance F=anchorSum F (fun L => ((noSix F univ∩localSeal univ L).card : ℚ))/
      (29*5005*sideWays) := by
    simp only [noHitChance,cutAvg,anchorSum,div_eq_mul_inv,←sum_mul]
    ring
  rw [eq]
  norm_num [sideWays,layoutWays,ways,longMass,Thirty.triples,Nat.fast_choose,Nat.factorial,Nat.choose_eq_fast_choose]
  linarith only [late_le_sample F]

theorem long_of_noHitChance (F : Factor V C)
    (chance : noHitChance F≤longPrice+(defect F : ℚ)/18000) :
    ((lateBad F).card : ℚ)/(ways 10 : ℚ)≤longMass*(longPrice+(defect F : ℚ)/18000) :=
  (late_fraction F).trans (mul_le_mul_of_nonneg_left chance (by native_decide))

theorem exact_of_noHitChance (g : WildExact.Coloring 30 29)
    (chance : noHitChance (coloringFactor g)≤longPrice+(defect (coloringFactor g) : ℚ)/18000) :
    WildExact.Exact g 20 := exact_of_long g (long_of_noHitChance _ chance)

end WildSieve.Thirty.Graph
