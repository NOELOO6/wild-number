import PairRows19
import SeparateRows19
namespace PairCuts19
def stirling : Nat → Nat → Nat
  | 0,0 => 1
  | 0,_+1 => 0
  | _+1,0 => 0
  | n+1,k+1 => stirling n k + (k+1)*stirling n (k+1)
def x (k : Nat) : Int := stirling k 2
def y (k : Nat) : Int := stirling k 3
def z (k : Nat) : Int := stirling k 4
def fail (k : Nat) : Int := if k≤1 then 0 else 1
def extra (k : Nat) : Int := (k-1 : Nat)

theorem split_products : ∀ a b : Fin 7,
    fail a ≤ x a-2*y a+6*z a ∧ extra a ≤ x a-y a+2*z a ∧
    x a*x b-2*y a*x b-2*x a*y b ≤ fail a*fail b ∧
    x a*x b-2*y a*x b-x a*y b ≤ fail a*extra b := by decide

theorem placement_units :
    factorial 19 = 5431826400*repeats ∧
    13218228559872000 = 590234400*repeats ∧
    468787544064000 = 20932800*repeats ∧
    5643509760000 = 252000*repeats ∧
    (590234400-2*20932800+6*252000 : Int) = 549880800 ∧
    (590234400-20932800+2*252000 : Int) = 569805600 := by decide

structure Draw where
  named : Fin 3
  other : Nat
def good (d : Draw) : Int := if d.named.val=0 ∧ d.other≤1 then 1 else 0
def sumBy (ds : List Draw) (f : Draw → Int) := (ds.map f).sum
def named (d : Draw) : Int := d.named.val
def other (d : Draw) : Int := d.other
def mixed (d : Draw) := named d * other d
def twins (d : Draw) : Int := if d.named.val=2 then 1 else 0

theorem one_point (d : Draw) (h : d.named.val≤1) :
    2-2*named d-other d+mixed d ≤ 2*good d := by
  rcases d with ⟨⟨n,hn⟩,o⟩
  change n≤1 at h
  have cases : n=0 ∨ n=1 := by omega
  rcases cases with rfl|rfl <;> simp [named,other,mixed,good] <;> (first | omega | split <;> omega)

theorem two_points (d : Draw) :
    4-4*named d-2*other d+4*twins d+mixed d ≤ 4*good d := by
  rcases d with ⟨⟨n,hn⟩,o⟩
  have cases : n=0 ∨ n=1 ∨ n=2 := by omega
  rcases cases with rfl|rfl|rfl <;> simp [named,other,mixed,good,twins] <;> (first | omega | split <;> omega)

theorem sum_one (ds : List Draw) (h : ∀ d∈ds, d.named.val≤1) :
    2*(ds.length : Int)-2*sumBy ds named-sumBy ds other+sumBy ds mixed ≤ 2*sumBy ds good := by
  induction ds with
  | nil => decide
  | cons d ds ih =>
    have v := one_point d (h d (by simp))
    have rest := ih (fun t ht => h t (by simp [ht]))
    simp only [List.length_cons,Int.natCast_add,Int.natCast_one,sumBy,List.map_cons,List.sum_cons] at *
    omega

theorem sum_two (ds : List Draw) :
    4*(ds.length : Int)-4*sumBy ds named-2*sumBy ds other+4*sumBy ds twins+sumBy ds mixed ≤ 4*sumBy ds good := by
  induction ds with
  | nil => decide
  | cons d ds ih =>
    have v := two_points d
    simp only [List.length_cons,Int.natCast_add,Int.natCast_one,sumBy,List.map_cons,List.sum_cons] at *
    omega

theorem one_color (ds : List Draw) (h : ∀ d∈ds, d.named.val≤1)
    (total : ds.length = 5431826400) (singles : sumBy ds named ≤ 549880800)
    (deficits : sumBy ds other ≤ 18*569805600) (pairs : 18*52111724 ≤ sumBy ds mixed) :
    222700716 ≤ sumBy ds good := by
  have bound := sum_one ds h
  omega

theorem two_colors (ds : List Draw) (total : ds.length = 5431826400)
    (singles : sumBy ds named ≤ 2*549880800) (others : sumBy ds other ≤ 17*549880800)
    (both : 50380208 ≤ sumBy ds twins) (pairs : 34*50380208 ≤ sumBy ds mixed) :
    136689976 ≤ sumBy ds good := by
  have bound := sum_two ds
  omega
/-- The number of extra pieces of the other colors when exactly one of the
two named colors fails. The separate-triple witnesses give a lower bound. -/
def exclusive (d : Draw) : Int := if d.named.val=1 then other d else 0

theorem with_credit (d : Draw) :
    4-4*named d-2*other d+4*twins d+mixed d+exclusive d ≤ 4*good d := by
  rcases d with ⟨⟨n,hn⟩,o⟩
  have cases : n=0 ∨ n=1 ∨ n=2 := by omega
  rcases cases with rfl|rfl|rfl <;> simp [named,other,mixed,good,twins,exclusive] <;>
    (first | omega | split <;> omega)

theorem credit_sum (ds : List Draw) :
    4*(ds.length : Int)-4*sumBy ds named-2*sumBy ds other+4*sumBy ds twins+
      sumBy ds mixed+sumBy ds exclusive ≤ 4*sumBy ds good := by
  induction ds with
  | nil => decide
  | cons d ds ih =>
    have v := with_credit d
    simp only [List.length_cons,Int.natCast_add,Int.natCast_one,sumBy,List.map_cons,List.sum_cons] at *
    omega

theorem two_colors_one_piece (ds : List Draw) (total : ds.length = 5431826400)
    (singles : sumBy ds named ≤ 2*549880800) (deficits : sumBy ds other ≤ 17*569805600)
    (both : 50380208 ≤ sumBy ds twins) (pairs : 34*52111724 ≤ sumBy ds mixed)
    (separate : 34*5246080 ≤ sumBy ds exclusive) : 26638742 ≤ sumBy ds good := by
  have bound := credit_sum ds
  omega
#print axioms two_colors_one_piece
#print axioms one_color
#print axioms two_colors
end PairCuts19
