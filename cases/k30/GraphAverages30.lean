import Histogram30
import SecondMeans30

namespace WildSieve.Thirty.Graph
open Finset
local instance (priority := 2000) avgEq : DecidableEq V := (inferInstance : LinearOrder V).toDecidableEq
set_option maxRecDepth 12000

theorem anchor_valid {F : Factor V C} {a : C} {L : Finset V} (h : L∈anchors F a) :
    L.card=12 ∧ Closed (F.f a) L := by
  obtain ⟨_,s,cl⟩ := candidate_mem.mp h
  exact ⟨s,by simpa only [empty_union] using cl⟩

theorem cut_mono (F : Factor V C) (f g : Finset V → ℚ)
    (h : ∀ a L,L∈anchors F a → f L≤g L) : cutAvg F f≤cutAvg F g := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact sum_le_sum (fun a _ => sum_le_sum (h a))

theorem cut_congr (F : Factor V C) (f g : Finset V → ℚ)
    (h : ∀ a L,L∈anchors F a → f L=g L) : cutAvg F f=cutAvg F g := by
  unfold cutAvg anchorSum
  congr 1
  exact sum_congr rfl (fun a _ => sum_congr rfl (h a))

@[simp] theorem cut_const (F : Factor V C) (b : ℚ) : cutAvg F (fun _ => b)=b := by
  rw [cutAvg,anchor_const]; ring

theorem cut_linear (F : Factor V C) (b : ℚ) (f g : Finset V → ℚ) :
    cutAvg F (fun L => b*f L+g L)=b*cutAvg F f+cutAvg F g := by
  unfold cutAvg anchorSum
  simp only [sum_add_distrib,←mul_sum]
  ring

theorem side_mono (L : Finset V) (f g : Deck → ℚ) (h : ∀ D∈localSeal univ L,f D≤g D) :
    sideAvg L f≤sideAvg L g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact sum_le_sum h

theorem side_congr (L : Finset V) (f g : Deck → ℚ) (h : ∀ D∈localSeal univ L,f D=g D) :
    sideAvg L f=sideAvg L g := by
  unfold sideAvg localSum
  rw [sum_congr rfl h]

@[simp] theorem side_zero (L : Finset V) : sideAvg L (fun _ => 0)=0 := by simp [sideAvg,localSum]

theorem side_const (L : Finset V) (sz : L.card=12) (b : ℚ) : sideAvg L (fun _ => b)=b := by
  simp only [sideAvg,localSum,sum_const,nsmul_eq_mul,seal_card L sz]
  exact (div_eq_iff (by decide : (sideWays : ℚ)≠0)).mpr (mul_comm _ _)

theorem side_linear (L : Finset V) (b : ℚ) (f g : Deck → ℚ) :
    sideAvg L (fun D => b*f D+g D)=b*sideAvg L f+sideAvg L g := by
  unfold sideAvg localSum
  simp only [sum_add_distrib,←mul_sum]
  ring

theorem frame_mono (F : Factor V C) (L : Finset V) (t : Fin 3) (f g : Pattern → ℚ)
    (h : ∀ P∈frames F L t,f P≤g P) : frameAvg F L t f≤frameAvg F L t g := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact sum_le_sum (fun P hp => mul_le_mul_of_nonneg_left (h P hp) (Nat.cast_nonneg _))

theorem frame_congr (F : Factor V C) (L : Finset V) (t : Fin 3) (f g : Pattern → ℚ)
    (h : ∀ P∈frames F L t,f P=g P) : frameAvg F L t f=frameAvg F L t g := by
  unfold frameAvg
  congr 1
  exact sum_congr rfl (fun P hp => congrArg (fun x : ℚ => (frameEvent L P).card*x) (h P hp))

@[simp] theorem frame_zero (F : Factor V C) (L : Finset V) (t : Fin 3) : frameAvg F L t (fun _ => 0)=0 := by
  simp [frameAvg]

theorem frame_linear (F : Factor V C) (L : Finset V) (t : Fin 3) (a : ℚ) (f g : Pattern → ℚ) :
    frameAvg F L t (fun P => a*f P+g P)=a*frameAvg F L t f+frameAvg F L t g := by
  unfold frameAvg
  simp only [mul_add,sum_add_distrib,mul_left_comm ((frameEvent _ _).card : ℚ) a,←mul_sum]
  ring

theorem frame_const (F : Factor V C) (L : Finset V) (sz : L.card=12) (t : Fin 3) (a : ℚ) :
    frameAvg F L t (fun _ => a)=a*conditionalMean F L t := by
  simpa only [mul_one,add_zero,frame_zero,frame_mass F L sz t] using
    frame_linear F L t a (fun _ => 1) (fun _ => 0)

theorem frame_sum {I : Type} [Fintype I] (F : Factor V C) (L : Finset V) (t : Fin 3) (f : I → Pattern → ℚ) :
    frameAvg F L t (fun P => ∑ i,f i P)=∑ i,frameAvg F L t (f i) := by
  unfold frameAvg
  simp only [mul_sum,div_eq_mul_inv,←sum_mul]
  rw [sum_comm]

def pop (F : Factor V C) (L : Finset V) (i : Fin 7) : ℚ :=
  ((univ : Finset C).filter (fun c => Inside F c L=i.val)).card

theorem pop_eq (F : Factor V C) (L : Finset V) (sz : L.card=12) (i : Fin 7) :
    pop F L i=cutPopulation F L sz i := by
  change ((univ.filter (fun c : C => Inside F c L=i.val)).card : ℚ) =
    ((univ.filter (fun c : C => leftType F L sz c=i)).card : ℚ)
  simp [leftType,Fin.ext_iff]

theorem mean_nonneg (F : Factor V C) (L : Finset V) (t : Fin 3) : 0≤conditionalMean F L t :=
  sum_nonneg (fun _ _ => weight_nonneg _ _ _)

end WildSieve.Thirty.Graph
