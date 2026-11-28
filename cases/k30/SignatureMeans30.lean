import GraphAverages30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) signatureEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 12000
set_option maxHeartbeats 800000

noncomputable def sigMean (F : Factor V C) (L : Finset V) (t : Fin 3) (w : Signature → ℚ) :=
  frameAvg F L t fun P => ∑ c,w (signatureOf F c (regionOf F L t P))

@[simp] theorem sig_zero (F : Factor V C) (L : Finset V) (t : Fin 3) : sigMean F L t (fun _ => 0)=0 := by
  simp [sigMean]

theorem sig_linear (F : Factor V C) (L : Finset V) (t : Fin 3) (a : ℚ) (f g : Signature → ℚ) :
    sigMean F L t (fun j => a*f j+g j)=a*sigMean F L t f+sigMean F L t g := by
  simp only [sigMean,sum_add_distrib,←mul_sum,frame_linear]

theorem sig_mass (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) :
    sigMean F L t (fun _ => 1)=29*conditionalMean F L t := by
  simp [sigMean,frame_const F L l]

theorem sig_edges (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) (k : Fin 10) :
    sigMean F L t (fun s => (s.cell k : ℚ))=(edgeTotal t k : ℚ)*conditionalMean F L t := by
  apply Eq.trans _ (frame_const F L l t (edgeTotal t k))
  apply frame_congr
  intro P hp
  rw [←Nat.cast_sum,signature_totals F (regionOf F L t P) t (region_spec F L l t P hp).sizes k]

theorem sig_anchor (F : Factor V C) (L : Finset V) (l : L.card=12) (a : C) (closed : Closed (F.f a) L)
    (t : Fin 3) : conditionalMean F L t ≤ sigMean F L t (fun s => if anchorClosed s t then 1 else 0) := by
  rw [←frame_mass F L l t]
  apply frame_mono
  intro P hp
  have bound := (frame_colors F L l a closed t P hp).2.2.1
  simp only [sum_boole]
  exact_mod_cast bound

theorem sig_population (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) (i : Fin 7) :
    sigMean F L t (fun s => if internal s t=i.val then 1 else 0)=pop F L i*conditionalMean F L t := by
  apply Eq.trans _ (frame_const F L l t (pop F L i))
  apply frame_congr
  intro P hp
  have spec := region_spec F L l t P hp
  simp only [internal_count,spec.left,sum_boole,pop]

theorem sig_closing (F : Factor V C) (L : Finset V) (l : L.card=12) (t : Fin 3) (i : Fin 7) :
    sigMean F L t (fun s => if internal s t=i.val ∧ labelClosed s then 1 else 0)=first t i*pop F L i := by
  classical
  let f (c : C) (P : Pattern) : ℚ := if Inside F c L=i.val then (if c∈owners F (vertices P) then 1 else 0) else 0
  have place : sigMean F L t (fun s => if internal s t=i.val ∧ labelClosed s then 1 else 0) =
      frameAvg F L t (fun P => ∑ c,f c P) := by
    apply frame_congr
    intro P hp
    apply sum_congr rfl
    intro c _
    have spec := region_spec F L l t P hp
    simp only [internal_count,spec.left,←mark_flag,spec.mark,←owner_mem,f,ite_and]
  rw [place,frame_sum]
  have term (c : C) : frameAvg F L t (f c)=if Inside F c L=i.val then first t i else 0 := by
    by_cases equal : Inside F c L=i.val
    · simpa only [f,equal,if_true] using frame_closing F L l t c
    · simp [f,equal]
  simp only [term,←sum_filter,sum_const,nsmul_eq_mul,pop]
  ring

theorem sig_other (F : Factor V C) (L : Finset V) (l : L.card=12) (t k : Fin 3) :
    secondMean F L t k≤sigMean F L t (otherBill t k) := second_bound F L l t k

theorem sig_complement (F : Factor V C) (L : Finset V) (l : L.card=12) :
    secondMean F L 0 0+sigMean F L 0 (fun s => complementCharge s-otherBill 0 0 s)≤conditionalMean F L 0 := by
  have h := complement_bound F L l
  change secondMean F L 0 0+sigMean F L 0 complementCharge ≤ sigMean F L 0 (otherBill 0 0)+conditionalMean F L 0 at h
  have eq := sig_linear F L 0 (-1) (otherBill 0 0) complementCharge
  simp only [neg_one_mul,neg_add_eq_sub] at eq
  rw [eq]
  linarith

end WildSieve.Thirty.Graph
