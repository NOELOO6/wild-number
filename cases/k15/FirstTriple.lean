import Teams
import BlockCatalogue
namespace FirstTriple
open Teams
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def X : Matching := [pair 1 2, pair 0 4, pair 3 5, pair 6 7, pair 8 9, pair 10 11, pair 12 13, pair 14 15]
def Y : Matching := [pair 0 1, pair 2 4, pair 3 5, pair 6 7, pair 8 9, pair 10 11, pair 12 13, pair 14 15]
def Z : Matching := [pair 0 4, pair 1 5, pair 2 6, pair 3 7, pair 8 9, pair 10 11, pair 12 13, pair 14 15]
def triples := unorderedTriples (List.range' 4 12) (fun i j k => pair i j ||| bit k)
def shut (m : Matching) (s : Nat) := m.all fun e => e &&& s == 0 || e &&& s == e
def lost (m : Matching) := triples.filter fun t => shut m (t ||| 1) || shut m (t ||| 14)
def degree (m : Matching) (v : Nat) := ((lost m).filter (fun t => t.testBit v)).length
theorem single_counts : triples.length = 220 ∧ (lost X).length = 10 ∧
    (lost Y).length = 0 ∧ (lost Z).length = 5 ∧ (List.range' 4 12).all (fun v =>
      degree X v == (if v == 4 || v == 5 then 5 else 2) &&
      degree Y v == 0 && degree Z v == (if v == 4 then 4 else 1)) = true := by native_decide

/-- An affine bound for twice the sum of squared vertex incidences. -/
theorem cap_vertex : (List.range 4).all (fun k => (List.range (19+3*k)).all
    (fun d => d*(d-1) ≤ 17*d+81*k)) = true := by decide
theorem cap_pair (d : Nat) : 6*d ≤ d*(d-1)+12 := by
  cases d with
  | zero => decide
  | succ d =>
    by_cases h : d ≤ 4
    · have cases : d=0 ∨ d=1 ∨ d=2 ∨ d=3 ∨ d=4 := by omega
      rcases cases with h|h|h|h|h <;> subst d <;> decide
    · have q := Nat.mul_le_mul_right d (show 6 ≤ d+1 by omega)
      simp only [Nat.succ_sub_one] at *
      omega

/-- If m distinct triples are excluded, at least three choices of the next
    allowed triple leave at most 29 exclusions on the final nine points. -/
theorem deficit : (List.range 76).all (fun m =>
    (30*(220-m) : Int) - (84*(m : Int)-(m : Int)*(m : Int)+34*(m : Int)+1035) ≥ 89) = true := by decide
theorem three_choices (cheap debt : Nat) (lower : 89 ≤ debt) (upper : debt ≤ 30*cheap) : 3 ≤ cheap := by omega

def small := BlockCatalogue.catalogue.filter (fun h => h.size ≤ 33)
theorem only_star : small.size = 1 ∧ small.all (fun h =>
    h.size == 28 && (Array.range 9).any (fun v => h.all (fun t => t.testBit v))) = true := by native_decide
theorem fourfold_bound : (List.range 76).all (fun m =>
    (34*(220-m) : Int) - (84*(m : Int)-(m : Int)*(m : Int)+34*(m : Int)+1035) ≥ 670) = true := by decide
theorem sparse_bound : (List.range 28).all (fun b => 34-b ≤ 280-10*b) = true := by decide
theorem group_count (layouts : Nat) (h : 670 ≤ 4*layouts) : 168 ≤ layouts := by omega
#print axioms single_counts
#print axioms only_star
end FirstTriple
