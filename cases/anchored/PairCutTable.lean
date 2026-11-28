import PairCutCounts

namespace WildAnchor.K30
open Finset
open scoped Classical

structure Profile where
  outside : Nat
  first : Nat
  second : Nat
  outsideFirst : Nat
  outsideSecond : Nat
  between : Nat
deriving DecidableEq

def profile (s : Colors3 (Fin 15)) : Profile :=
  ⟨sizeThree s 0,sizeThree s 1,sizeThree s 2,sizeThree s 3,sizeThree s 4,sizeThree s 5⟩

private theorem same_profile {s t : Colors3 (Fin 15)} (h : profile s=profile t) :
    ∀ j,sizeThree s j=sizeThree t j := by
  intro j
  have options : ∀ z : Fin 6,z=0 ∨ z=1 ∨ z=2 ∨ z=3 ∨ z=4 ∨ z=5 := by decide
  rcases options j with rfl|rfl|rfl|rfl|rfl|rfl
  · exact congrArg Profile.outside h
  · exact congrArg Profile.first h
  · exact congrArg Profile.second h
  · exact congrArg Profile.outsideFirst h
  · exact congrArg Profile.outsideSecond h
  · exact congrArg Profile.between h

private def sourceMass (k : Profile) : Nat := ∑ q : DoubleCut,
  if profile (source3 q)=k then (∏ i,(sizeThree (source3 q) i).factorial)*2^diagonal (source3 q) else 0

/-- Each entry is the total shuffle multiplicity of source cuts with these
six unordered edge counts, in the field order of Profile. -/
private def weights22 : List (Profile × Nat) := [
  (⟨5,0,1,5,3,1⟩,11059200),
  (⟨5,0,2,6,2,0⟩,88473600),
  (⟨5,1,0,3,5,1⟩,11059200),
  (⟨5,1,1,4,4,0⟩,141557760),
  (⟨5,2,0,2,6,0⟩,221184000),
  (⟨6,0,0,3,3,3⟩,9953280),
  (⟨6,0,1,4,2,2⟩,97320960),
  (⟨6,0,2,5,1,1⟩,442368000),
  (⟨6,1,0,2,4,2⟩,70778880),
  (⟨6,1,1,3,3,1⟩,431308800),
  (⟨6,1,2,4,2,0⟩,1238630400),
  (⟨6,2,0,1,5,1⟩,973209600),
  (⟨6,2,1,2,4,0⟩,3220439040),
  (⟨7,0,1,3,1,3⟩,139345920),
  (⟨7,0,2,4,0,2⟩,1486356480),
  (⟨7,1,0,1,3,3⟩,139345920),
  (⟨7,1,1,2,2,2⟩,908328960),
  (⟨7,1,2,3,1,1⟩,3096576000),
  (⟨7,2,0,0,4,2⟩,1981808640),
  (⟨7,2,1,1,3,1⟩,6440878080),
  (⟨7,2,2,2,2,0⟩,16019619840),
  (⟨8,1,1,1,1,3⟩,1238630400),
  (⟨8,1,2,2,0,2⟩,6606028800),
  (⟨8,2,1,0,2,2⟩,5945425920),
  (⟨8,2,2,1,1,1⟩,13872660480)]

private theorem calibrated : weights22.all (fun e => decide (e.2≤sourceMass e.1))=true := by native_decide

def reward (k : Profile) := ((weights22.find? (fun e => decide (e.1=k))).map Prod.snd).getD 0

private theorem reward_le (k : Profile) : reward k≤sourceMass k := by
  unfold reward
  generalize h : weights22.find? (fun e => decide (e.1=k))=v
  cases v with
  | none => simp
  | some z =>
    have mem := List.mem_of_find?_eq_some h
    have test := List.find?_some h
    have eq : z.1=k := of_decide_eq_true test
    simpa [eq] using of_decide_eq_true (List.all_eq_true.mp calibrated z mem)

theorem reward_row (t : Colors3 (Fin 15)) :
    reward (profile t)≤∑ q : DoubleCut,priceThree (source3 q) t := by
  apply (reward_le _).trans
  apply sum_le_sum
  intro q _
  by_cases eq : profile (source3 q)=profile t
  · simp [eq,priceThree,same_profile eq]
  · simp [eq]

def pairBill (next : Equiv.Perm (Fin 15)) : Nat :=
  ∑ k∈picks,reward (profile (row3 next k))

theorem pairBill_le (next : Equiv.Perm (Fin 15)) :
    pairBill next≤∑ q : DoubleCut,∑ k∈picks,priceThree (source3 q) (row3 next k) := by
  unfold pairBill
  rw [sum_comm (s:=univ) (t:=picks)]
  exact sum_le_sum fun k _ => reward_row _

end WildAnchor.K30
