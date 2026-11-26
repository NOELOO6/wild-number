import LastTwoRows
import SquareRows
namespace LastTwoBound

def cap (k : Nat) : Int := 2000000 / (k : Int)
def pairs (k : Nat) := k*(k-1)/2
def wins (k : Nat) : Int := if k=0 then 1 else 0
def sumBy {α} (xs : List α) (f : α → Int) := (xs.map f).sum

structure Grouping where
  failed : Fin 14
  credits : List Int
def grouped (g : Grouping) : Prop :=
  g.credits.length = pairs g.failed ∧ ∀ v ∈ g.credits, v ≤ cap g.failed

private theorem cap_sum (xs : List Int) (v : Int) (h : ∀ x ∈ xs, x ≤ v) :
    xs.sum ≤ (xs.length : Int)*v := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have one := h x (by simp)
    have rest := ih (fun y hy => h y (by simp [hy]))
    simp only [List.sum_cons,List.length_cons,Int.natCast_add,Int.natCast_one,Int.add_mul,Int.one_mul]
    omega

theorem grouping_credit (g : Grouping) (hg : grouped g) :
    1000000*(1-(g.failed.val : Int))+g.credits.sum ≤ 1000000*wins g.failed := by
  have rates : ∀ k : Fin 14, 1000000*(1-(k.val : Int))+(pairs k : Int)*cap k ≤ 1000000*wins k := by decide
  have b := cap_sum g.credits (cap g.failed) hg.2
  rw [hg.1] at b
  have := rates g.failed
  omega

theorem combine (xs : List Grouping) (h : ∀ g ∈ xs, grouped g) :
    1000000*((xs.length : Int)-sumBy xs (fun g => g.failed.val))+sumBy xs (fun g => g.credits.sum)
       ≤ 1000000*sumBy xs (fun g => wins g.failed) := by
  induction xs with
  | nil => decide
  | cons g xs ih =>
    have one := grouping_credit g (h g (by simp))
    have rest := ih (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons,Int.natCast_add,Int.natCast_one,sumBy,List.map_cons,List.sum_cons] at *
    omega

/-- The 78 named pairs each supply the audited integer gain after all
third-color charges and their cancelling transfers have been counted. -/
theorem at_least_449107 (xs : List Grouping) (h : ∀ g ∈ xs, grouped g)
    (layouts : xs.length = 22422400) (singles : sumBy xs (fun g => g.failed.val) = 13*3068800)
    (pairsAudit : 78*229757771206 ≤ sumBy xs (fun g => g.credits.sum)) :
    449107 ≤ sumBy xs (fun g => wins g.failed) := by
  have b := combine xs h
  rw [layouts,singles] at b
  omega
/-- Of the groupings passing the thirteen specified colors, remove those in
which both outside colors fail. In each row the discarded groupings avoid
every configuration already charged to one of the thirteen named colors. -/
def reclaimed (i : Fin 7) := if i.val=6 then 113020 else LastTwo.thirdMin[i.val]!
def room (i : Fin 7) := LastTwo.joint[i.val]! - reclaimed i

theorem outside_bound : ∀ i : Fin 7, room i ≤ 440580 := by decide
theorem at_least_8527 (i : Fin 7) (passing bothFail oneOrBoth : Nat)
    (prefixCount : 449107 ≤ passing) (split : passing = bothFail+oneOrBoth)
    (bad : bothFail ≤ room i) : 8527 ≤ oneOrBoth := by
  have := outside_bound i
  omega
#print axioms at_least_449107
#print axioms at_least_8527
end LastTwoBound
