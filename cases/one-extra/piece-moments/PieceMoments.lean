import Lean.Data.Json
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace WildExact.PieceMoments
open Lean Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Convert a lower bound on the excess above two into a count of nearly winning layouts. -/
theorem near_count {Ω : Type} [Fintype Ω] (d : Ω → Nat) (credit : ℚ)
    (paid : credit ≤ ∑ x : Ω,((d x-2 : Nat) : ℚ)) :
    let near := (univ : Finset Ω).filter (fun x => d x≤1)
    2*(Fintype.card Ω : ℚ) + credit ≤ 2*(near.card : ℚ)+∑ x : Ω,(d x : ℚ) := by
  classical
  let near := (univ : Finset Ω).filter (fun x => d x≤1)
  have localBound (x : Ω) : 2+((d x-2 : Nat) : ℚ) ≤ (if d x≤1 then 2 else 0)+(d x : ℚ) := by
    by_cases h : d x≤1
    · simp [h,show d x-2=0 by omega]
    · have eq : d x=2+(d x-2) := by omega
      simp only [if_neg h]
      exact_mod_cast (show 2+(d x-2)≤0+d x by omega)
  have total := sum_le_sum (s:=(univ : Finset Ω)) (fun x _ => localBound x)
  have cnt : (∑ x : Ω,if d x≤1 then (2 : ℚ) else 0)=(near.card : ℚ)*2 := by
    rw [←sum_filter]; simp [near]
  simp only [sum_add_distrib,sum_const,card_univ,nsmul_eq_mul,cnt] at total
  dsimp only
  linarith

structure Certificate where
  affine : Array String
  multipliers : Array (Array (Array String))
  deriving Inhabited, FromJson

structure Row where
  n : Nat
  frame : Option (Array Nat)
  certificate : Option Certificate := none
  protect : Array Nat
  per_million : Array Nat
  deriving Inhabited, FromJson

def rows : Array Row := ((Json.parse (include_str "certificates.json")).bind fromJson?).toOption.get!

def rational (s : String) : ℚ :=
  let parts := s.splitOn "/"
  (parts[0]!.toInt! : ℚ)/(parts[1]?.getD "1").toNat!

def choose (n k : Nat) : Nat := Nat.fast_choose n k

/-- Conditional extension bounds multiplied along an ordered frame through the root. -/
def frameFraction (n size : Nat) (allowCollisions : Bool) : ℚ :=
  (List.range (size-1)).foldl (fun prob j =>
    let b := j+1
    let outside := n+1-b
    let charge := choose b 2*(b-2)
    let cap := if allowCollisions then charge/outside else 0
    prob*((outside-charge/(cap+1) : Nat) : ℚ)/outside) 1

theorem uniform_layout_bounds :
    (33298 : ℚ) ≤ 1000*1266*frameFraction 69 7 false ∧
    (891247 : ℚ) ≤ 1000*13520*frameFraction 75 7 false ∧
    (191 : ℚ) ≤ 1000*12377*frameFraction 37 8 true/35 ∧
    (88 : ℚ) ≤ 1000*1808*frameFraction 43 8 true/35 := by native_decide

def pairings (k : Nat) := if k%2=1 then 0 else
  (List.range (k/2)).foldl (fun z i => z*(2*i+1)) 1

def completions (planted : Bool) (h b : Nat) : Nat :=
  let u := 3*h
  if !planted then pairings (u+b)
  else if b≤u then (List.range b).foldl (fun z i => z*(u-i)) 1 * pairings (u-b)
  else 0

def width (ds : Array Nat) (mask : Nat) : Nat := Id.run do
  let mut z := 0
  for i in [:ds.size] do
    if mask.testBit i then z := z+ds[i]!
  return z

/-- Choose the component of a distinguished block. Smaller subproblems precede the
current state in increasing order of the number of free triples and the part mask. -/
def profile (planted : Bool) (t : Nat) (ds : Array Nat) : ℚ × ℚ := Id.run do
  let masks := 2^ds.size
  let full := masks-1
  let widths := (Array.range masks).map (width ds)
  let mut connected : Array Nat := #[]
  for h in [:t+1] do
    for s in [:masks] do
      let mut loss := 0
      if h+s>0 then
        for l in [:h+1] do
          for j in [:s+1] do
            if j &&& s != j || (h == l && s == j) then continue
            let anchored := if s == 0 then 0<l else (j &&& (s ^^^ (s &&& (s-1)))) != 0
            if !anchored then continue
            let choices := if s == 0 then choose (h-1) (l-1) else choose h l
            loss := loss + choices*connected[l*masks+j]!*completions planted (h-l) widths[s-j]!
      let total := completions planted h widths[s]!
      connected := connected.push (if h+s == 0 then 0 else total-loss)
  let den := completions planted t widths[full]!
  let mut pieces := 0
  for h in [:t+1] do
    for s in [:masks] do
      if s%2 == 0 then
        pieces := pieces+choose t h*connected[h*masks+s]!*completions planted (t-h) widths[full-s]!
  return (((den-connected[t*masks+full]! : Nat) : ℚ)/den,(pieces : ℚ)/den)

def means (n : Nat) (frame : Option (Array Nat)) : ℚ × ℚ := Id.run do
  let f := #[0,4,5][n%3]!
  let ds := #[1]++(frame.getD (if f == 0 then #[] else #[f]))
  let b := ds.foldl (·+·) 0
  let t := (n+1-b)/3
  let initial := profile frame.isSome t ds
  let count := if frame.isSome then n-choose b 2 else n
  let mut fail := count*initial.1
  let mut deficit := count*initial.2
  if frame.isSome then
    for i in [:ds.size] do
      for j in [:i+1] do
        let m := if i == j then choose ds[i]! 2 else ds[i]! * ds[j]!
        if m == 0 then continue
        let new := if i == j then ds.set! i (ds[i]!-2) else
          (ds.set! j (ds[i]!+ds[j]!-2)).eraseIdx! i
        let v := profile true t new
        fail := fail+m*v.1
        deficit := deficit+m*v.2
  return (fail,deficit)

def elementary (a b c : Nat) : Array Nat :=
  let p := a+2*b+3*c
  let q := a+4*b+9*c
  let r := a+8*b+27*c
  #[1,p,(p*p-q)/2,(p^3+2*r-3*p*q)/6]

def credit (n b : Nat) (p : Certificate) : Option ℚ := Id.run do
  if p.affine.size != 2 || p.multipliers.size != 3 then return none
  let u := n+1-b
  let t := u/3
  let s0 := rational p.affine[0]!
  let s1 := rational p.affine[1]!
  let mut coefficients : Array (Array ℚ) := #[]
  for row in p.multipliers do
    if row.size != 3 then return none
    let mut v := Array.replicate 4 (0 : ℚ)
    for j in [:3] do
      let pair := row[j]!
      if pair.size != 2 then return none
      let l := rational pair[0]!
      let h := rational pair[1]!
      if l<0 || h<0 then return none
      let q := u-3*(j+1)
      let den := choose (q-1) 2*(j+1)
      if den == 0 then return none
      let lo : ℚ := (q*(q-(n+1)/2) : Nat)/ (den : ℚ)
      let hi : ℚ := (q*((q-1)/2) : Nat)/ (den : ℚ)
      v := v.set! j (v[j]!-l*lo+h*hi)
      v := v.set! (j+1) (v[j+1]!+l-h)
    coefficients := coefficients.push v
  for a in [:t+1] do
    for b' in [:t-a+1] do
      for c in [:t-a-b'+1] do
        let xs := #[a,b',c]
        let z := a+2*b'+3*c
        let mut score := s0+s1*z
        for i in [:3] do
          if xs[i]! == 0 then continue
          let rest := xs.set! i (xs[i]!-1)
          let es := elementary rest[0]! rest[1]! rest[2]!
          for j in [:4] do
            score := score+xs[i]!*coefficients[i]![j]!*es[j]!
        if score>(z-2 : Nat) then return none
  let marks := u*((u-b)/2)+choose (b-1) 2
  return some (s0+s1*marks/choose (u-1) 2)

def protectedCount (r : Row) (m : ℚ × ℚ) (gain : ℚ) : Array Nat := Id.run do
  let mut rooted := m.1/r.n
  let mut worst := rooted
  if let some frame := r.frame then
    let ds := #[1]++frame
    let t := (r.n+1-ds.foldl (·+·) 0)/3
    rooted := 0
    worst := (profile true t ds).1
    for i in [:ds.size] do
      for j in [:i+1] do
        if i == j && ds[i]!<2 then continue
        let changed := if i == j then ds.set! i (ds[i]!-2) else
          (ds.set! j (ds[i]!+ds[j]!-2)).eraseIdx! i
        let fail := (profile true t changed).1
        worst := max worst fail
        if j == 0 then rooted := max rooted fail
  let allowed (mean weight threshold : ℚ) := (List.range (r.n+1)).foldl (fun best k =>
    if mean+weight*((min 2 k : Nat)*rooted+(k-2 : Nat)*worst)<threshold then k else best) 0
  return #[allowed (m.2-gain) 1 2, allowed (m.1-gain) 1 2, allowed m.2 2 3]

/-- If a named color fails, it contributes to the total deficit as well as its penalty. -/
theorem protected_budget (d named cap : Nat) (bounded : named≤d)
    (h : d+cap*named≤cap) : d≤cap ∧ named=0 := by
  constructor
  · omega
  · by_contra bad
    have pos : 1≤named := by omega
    have enough : cap≤cap*named := by simpa using (Nat.mul_le_mul_left cap pos)
    omega

def test (r : Row) : Bool := Id.run do
  let b := 1+(r.frame.getD #[]).foldl (·+·) 0
  if r.frame.isSome then
    let f := #[0,4,5][r.n%3]!
    let groups := r.frame.get!
    if !groups.all (fun v => v == 3 || (f != 0 && v == f)) || (f != 0 && (groups.filter (fun v => v == f)).size != 1) then return false
    if (r.n+1-b)%3 != 0 || !(List.range b).all (fun k => k+choose k 2*(k-2)<r.n+1) then return false
  let some gain := (r.certificate.map (credit r.n b)).getD (some 0) | return false
  let m := means r.n r.frame
  let perMillion (x : ℚ) :=
    let y := max 0 x*1000000
    (y.num/y.den).toNat
  return r.protect == protectedCount r m gain && r.per_million == #[perMillion (1-(m.2-gain)/2),perMillion (1-(m.1-gain)/2),perMillion (1-m.2/3)]

theorem all_orders : rows.map Row.n=#[15]++(Array.range 29).map (fun i => 19+2*i) := by native_decide
theorem all_certificates : rows.all test=true := by native_decide

#print axioms near_count
#print axioms all_certificates
end WildExact.PieceMoments
