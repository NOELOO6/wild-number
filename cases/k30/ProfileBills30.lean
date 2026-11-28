import CellSpectrum30
import SealSpectrum

namespace WildSieve.Thirty.Graph
open Finset
set_option maxRecDepth 10000

def profileSpectrum (s : Signature) (n : Nat) : Multiset (Multiset (Fin 4)) :=
  ((((cellList s : Multiset (Fin 10)).map ends).powersetCard n).map Multiset.sum)

def sideSignature (n i : Nat) : Signature := ⟨0,0,0,0,0,0,0,i,n-2*i,15-n+i⟩

/-- Completions of the free regions after two distinguished triples have been
prescribed. Partial intersections with a distinguished triple cannot be sealed. -/
def otherCompletions (t k : Nat) (p : Multiset (Fin 4)) : Nat :=
  let a := p.count 0
  let b := p.count 1
  let l := p.count 2
  let r := p.count 3
  let rightPoints := (if t=2 then a else 0)+(if t=0 then 0 else b)+r
  if a%3=0 ∧ b%3=0 ∧ a+b<6 ∧ rightPoints=3*k then
    sealWays (leftFree t) l * sealWays (24-leftFree t) r
  else 0

def otherDenom (t : Nat) := layoutWays (leftFree t)*layoutWays (24-leftFree t)

def profileTotal (s : Signature) (n : Nat) (w : Multiset (Fin 4) → Nat) :=
  ((profileSpectrum s n).map w).sum

def givenSide (t : Nat) (p : Multiset (Fin 4)) :=
  if p.count 2=6-3*t then sealWays 12 (p.count 2)*sealWays 18 (p.count 3) else 0

def chosenSide (t : Nat) (p : Multiset (Fin 4)) := if p.count 2=6-3*t then 1 else 0

private theorem first_table : ∀ i : Fin 7, ∀ t : Fin 3,
    (profileTotal (sideSignature 12 i) 3 (givenSide t) : ℚ)=first t i*(layoutWays 12*layoutWays 18 : Nat) := by
  native_decide

private theorem duplicate_table : ∀ i : Fin 4, ∀ t : Fin 3,
    (profileTotal (sideSignature 6 i) 6 (chosenSide t) : ℚ)*factor 12 18 t =
      duplicateWeight t i*(Nat.choose 15 6) := by native_decide

private theorem other_table : ∀ t : Fin 3, ((signatures t).all fun s =>
    (List.finRange 3).all fun k => decide
      ((profileTotal s 3 (otherCompletions t k) : ℚ)=otherBill t k s*otherDenom t))=true := by
  native_decide

theorem graph_profile_total (F : Factor V C) (c : C) (z : V → Fin 4) (n : Nat)
    (w : Multiset (Fin 4) → Nat) :
    (∑ Q∈candidates F c ∅ univ (2*n), w (Q.val.map z)) =
      profileTotal (signatureOf F c z) n w := by
  rw [profileTotal,profileSpectrum,←cell_spectrum F c z n,Multiset.map_map]
  rfl

theorem other_completions_sum (F : Factor V C) (c : C) (z : V → Fin 4)
    (t k : Fin 3) (sizes : ∀ j,(zone z j).card=zoneSize t j) :
    ((∑ Q∈candidates F c ∅ univ 6,otherCompletions t k (Q.val.map z) : Nat) : ℚ)=
      otherBill t k (signatureOf F c z)*otherDenom t := by
  have h := List.all_eq_true.mp (other_table t) _ (mem_signatures (signature_fits F c z t sizes))
  have val := of_decide_eq_true (List.all_eq_true.mp h k (List.mem_finRange _))
  rw [←graph_profile_total] at val
  exact val

theorem first_completions_sum (F : Factor V C) (c : C) (z : V → Fin 4)
    (t : Fin 3) (i : Fin 7) (sg : signatureOf F c z=sideSignature 12 i) :
    ((∑ Q∈candidates F c ∅ univ 6,givenSide t (Q.val.map z) : Nat) : ℚ)=
      first t i*(layoutWays 12*layoutWays 18 : Nat) := by
  have h := first_table i t
  rw [←sg,←graph_profile_total] at h
  exact h

theorem duplicate_completions_sum (F : Factor V C) (c : C) (z : V → Fin 4)
    (t : Fin 3) (i : Fin 4) (sg : signatureOf F c z=sideSignature 6 i) :
    ((∑ Q∈candidates F c ∅ univ 12,chosenSide t (Q.val.map z) : Nat) : ℚ)*factor 12 18 t =
      duplicateWeight t i*(Nat.choose 15 6) := by
  have h := duplicate_table i t
  rw [←sg,←graph_profile_total] at h
  exact h

#print axioms other_completions_sum
end WildSieve.Thirty.Graph
