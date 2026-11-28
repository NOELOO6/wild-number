import PairCutCheck15

namespace PairCutCheck15
set_option interpreter.prefer_native true

def choose (n : Nat) : Nat → Nat
  | 0 => 1
  | 1 => n
  | 2 => n*(n-1)/2
  | _ => n*(n-1)*(n-2)/6

def weight (j : Nat) := ((j%2)+((j/2)%2)+j/4)
def isum {α : Type} (xs : List α) (f : α → Int) : Int := (xs.map f).sum

/-- Three times the symmetrized score on one layout. -/
def score (g : Goal) (p r : Nat) : Int :=
  let a := (prices g).a
  let term (d k : Nat) : Int := (choose p (d-k) : Int)*(choose r k : Int)
  3*(a[0]!+a[1]!*(p : Int)+a[2]!*(r : Int)+isum (List.range 3) (fun j => a[3+j]!*term 2 j))+
    isum (List.range 8) (fun j => (if weight j==0 || weight j==3 then 3 else 1)*a[6+j]!*term 3 (weight j))

def succeeds (g : Goal) (p r : Nat) : Int :=
  if (p : Int)≤(prices g).header[2]! ∧ (r : Int)≤(prices g).header[1]! then 1 else 0

def scale (g : Goal) := (prices g).header[0]!
def bound (g : Goal) := (prices g).header[5]!
def base (g : Goal) :=
  let a := (prices g).a
  1401400*a[0]!+15*(91000*a[1]!+100800*a[2]!)
def gain (g : Goal) (i : Fin 11) := (prices g).rows[i.val]!.gain
def least (g : Goal) := ((prices g).rows.map Row.gain).toList.foldl min 10000000000000000
def selected (g : Goal) (i : Fin 11) : Bool :=
  let id := (prices g).header[4]!.toNat
  if id==11 then (prices g).rows[i.val]!.cycles[0]! == 4 else i.val==id
def selectedGain (g : Goal) :=
  ((List.finRange 11).filter (selected g)).foldl (fun z i => min z (gain g i)) 10000000000000000
def bonus (g : Goal) := selectedGain g-least g
def special (g : Goal) (i : Fin 11) : Int := if selected g i then 1 else 0
def required (g : Goal) := (prices g).header[3]!

def scalarOK (g : Goal) :=
  (List.range 16).all (fun p => (List.range (16-p)).all fun r => score g p r≤3*scale g*succeeds g p r) &&
  (List.finRange 11).all (fun i => least g+special g i*bonus g≤gain g i) &&
  (List.finRange 11).all (fun i => (List.finRange 11).all fun j => (List.finRange 11).all fun k =>
    let fee (x y z : Fin 11) := (prices g).rows[x.val]!.transfer[11*y.val+z.val]!
    fee i j k==fee i k j && 0≤fee i j k+fee j i k+fee k i j) &&
  decide (0≤bonus g ∧ 0<scale g ∧
    105*scale g*(bound g-1)<105*(base g+least g)+required g*bonus g)

theorem scalars (g : Goal) : scalarOK g=true := by cases g <;> native_decide

private theorem lower_per_pair (g : Goal) (i : Fin 11) : least g+special g i*bonus g≤gain g i := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (scalars g)).1).1).2
  have m : i∈List.finRange 11 := by
    have hz : i.val < (List.finRange 11).length := by simp
    have inside := List.getElem_mem (l:=List.finRange 11) hz
    simpa using inside
  exact of_decide_eq_true (List.all_eq_true.mp h i m)

private theorem sum_gain (g : Goal) (is : List (Fin 11)) :
    (is.length : Int)*least g+isum is (special g)*bonus g≤isum is (gain g) := by
  induction is with
  | nil => simp [isum]
  | cons i is ih =>
    have h := lower_per_pair g i
    simp only [isum,List.map_cons,List.sum_cons,List.length_cons,Int.natCast_add,Int.natCast_one,
      Int.add_mul,Int.one_mul] at *
    omega

private theorem sum_score (g : Goal) (xs : List (Nat × Nat)) (cap : ∀ v∈xs,v.1+v.2≤15) :
    isum xs (fun v => score g v.1 v.2) ≤ 3*scale g*isum xs (fun v => succeeds g v.1 v.2) := by
  have h := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (scalars g)).1).1).1
  induction xs with
  | nil => simp [isum]
  | cons x xs ih =>
    have small := cap x (by simp)
    have q := List.all_eq_true.mp h x.1 (List.mem_range.mpr (by omega))
    have r := of_decide_eq_true (List.all_eq_true.mp q x.2 (List.mem_range.mpr (by omega)))
    have rest := ih (fun v hv => cap v (by simp [hv]))
    simp only [isum,List.map_cons,List.sum_cons,Int.mul_add] at *
    omega

/-- Aggregate the checked score on any layout census whose matching accounts give the indicated
lower bound. The graph-to-account double count is in the accompanying proof. -/
theorem count_from_accounts (g : Goal) (xs : List (Nat × Nat)) (types : List (Fin 11))
    (cap : ∀ v∈xs,v.1+v.2≤15) (pairs : types.length=105)
    (enough : required g≤isum types (special g))
    (account : 315*base g+3*isum types (gain g)≤105*isum xs (fun v => score g v.1 v.2)) :
    bound g≤isum xs (fun v => succeeds g v.1 v.2) := by
  have num := of_decide_eq_true (Bool.and_eq_true_iff.mp (scalars g)).2
  obtain ⟨nonneg,pos,strict⟩ := num
  have rows := sum_gain g types
  rw [pairs] at rows
  have extra := Int.mul_le_mul_of_nonneg_right enough nonneg
  have scoreBound := sum_score g xs cap
  apply Classical.byContradiction
  intro bad
  have small : isum xs (fun v => succeeds g v.1 v.2)≤bound g-1 := by omega
  have m := Int.mul_le_mul_of_nonneg_left small (show 0≤3*scale g by omega)
  have D : scale g=1000000 := by cases g <;> native_decide
  have budget := Int.mul_le_mul_of_nonneg_left (Int.le_trans scoreBound m) (by decide : (0:Int)≤105)
  rw [D] at budget strict
  omega

end PairCutCheck15
