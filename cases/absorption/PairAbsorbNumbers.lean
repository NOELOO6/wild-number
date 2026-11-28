import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Nat.Choose.Basic

namespace WildExact.PairAbsorbNumbers
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def C (n k : Nat) := Nat.fast_choose n k

/-- Pair and color incidences for the distinguished pair and a remaining q-set. -/
def marks (n : Nat) := C n 2 - 3*(n-1) + 3
def allowed (n m q used : Nat) : Nat × Nat :=
  let u := n-2
  let d := 3*((n-1)/2)
  let D := 3*(u-1)/2
  let k := n-q
  let low := max (C n 2+2*C k 2-d*k) (max (q*(q-(n+1)/2)) (marks n-(u-q)*D))
  let high := min (C q 2) (min (C n 2+3*C k 2-d*k-used) (marks n))
  (max ((low+2)/3) (max (low-(marks n-m)) (m-(u-q)*D)),
   min (C q 3) (min high (m-max used ((marks n-high+2)/3))))

structure Interval where
  lo : Int
  hi : Int
  den : Nat
  deriving Inhabited

def scaleBack (l h scale : Nat) (later : Interval) : Interval :=
  let den := scale*later.den
  ⟨(den : Int)-(if 0≤later.hi then h else l)*later.hi,
   (den : Int)-(if 0≤later.lo then l else h)*later.lo,den⟩

def interval (n m q k start : Nat) (thin : Bool) : Interval := Id.run do
  let mut ans : Interval := ⟨1,1,1⟩
  let (a,h) := allowed n m q 0
  for i in [:k-start] do
    let j := k-1-i
    let v := q-3*j
    let (l',h') := allowed n m v j
    let l := if thin then max (a-3*j*(3*(q-1)/2)) (l'-(h-a)) else l'
    let hi := if thin then min (a-j) h' else h'
    ans := scaleBack l hi ((j+1)*C (v-1) 2) ans
  return ans

def avoidance (n m q : Nat) : ℚ × ℚ := Id.run do
  let mut lower : ℚ := 0
  let mut upper : ℚ := 1
  let a := (allowed n m q 0).1
  let den := C (q-1) 2
  let pairs := min (a*(a-1)) (a*(a+8)-(9*a*a+q-1)/q)
  for i in [:min 6 (q/3)] do
    let k := i+1
    let raw := interval n m q k 0 false
    if k%2==1 then lower := max lower ((raw.lo : ℚ)/raw.den)
    else
      upper := min upper ((raw.hi : ℚ)/raw.den)
      if a>0 then
        let tail := interval n m q k 2 true
        if tail.hi≥0 then
          let bound : ℚ := 1-(a : ℚ)/den+
            ((pairs : ℚ)*tail.hi)/(2*den*C (q-4) 2*tail.den : Nat)
          upper := min upper bound
  return (lower,upper)

def partitions : Nat → Nat
  | 0 => 1
  | j+1 => C (3*j+2) 2*partitions j

def sides (u forced inside j : Nat) (rootOnly : Bool) :=
  if (rootOnly && j==1) || 3*j<inside || (3*j-inside)%2!=0 then 0
  else C ((u-forced)/2) ((3*j-inside)/2)

def mass (n j : Nat) : ℚ :=
  let u := n-2
  let t := u/3
  let generic := sides u 3 0 j false + sides u 3 1 j true +
    sides u 3 2 j false + sides u 3 3 j false
  let linked := sides u 1 0 j false + sides u 1 1 j false
  let outside := sides u 1 0 j false + sides u 1 1 j true
  let incidences := (n-3)*generic + 2*linked + 2*outside
  (incidences*partitions j*partitions (t-j) : Nat)/(partitions t : ℚ)

def allCounts (n target : Nat) : Bool := Id.run do
  let u := n-2
  let massAt := (Array.range ((u/3)/2)).map fun i => mass n (i+1)
  for m in [(marks n+2)/3:marks n+1] do
    let mut total : ℚ := 0
    for j in [:massAt.size] do
      total := total+massAt[j]!*(avoidance n m (u-3*(j+1))).2
    if 1000000*(2*(avoidance n m u).1-total)<2*target then return false
  return true

theorem K59 : allCounts 59 4472=true := by native_decide
theorem K65 : allCounts 65 43846=true := by native_decide
theorem K71 : allCounts 71 73125=true := by native_decide
#print axioms K59
end WildExact.PairAbsorbNumbers
