import Twelve
namespace LastTwo
open Prescribed WildTwelve
set_option maxRecDepth 200000

def prices := parseRows (include_str "free-tangent.txt") 7 13

def audit (i : Nat) := Id.run do
  let r := prices[i]!
  let row := r.row
  let (a,b) := canonical row.cycles
  let ca := closed a
  let cb := closed b
  let ia := internal a
  let ib := internal b
  let mut ct : Counts := ⟨0,0,Array.replicate 65536 0,Array.replicate (1820*8008) 0⟩
  for root in [:16] do
    ct := WildTwelve.layouts r ca cb ia ib 5 (65535 ^^^ bit root) #[bit root] false false ct
  let mut edgeBill : Int := 0
  for y in [:16] do
    for x in [:y] do
      if a[x]! != y && b[x]! != y then edgeBill := edgeBill+row.edge[pairId x y]!
  let gain := (ct.both : Int)-edgeBill-11*row.selected-2*row.omitted
  let table := keyTable (prices.map Tangent.row)
  return r.valid && ct.one == 3068800 && ct.both == r.weighted && gain == row.gain &&
    row.gain ≥ 229757771206 && eachThird false table row ct a b 8 65535
      (Array.replicate 16 0) #[] 0 1 == (expected false)[i]!

def cancelled := (Array.range 7).all fun i => (Array.range 7).all fun j => (Array.range 7).all fun k =>
  let fee := fun x y z : Nat => prices[x]!.row.transfer[y]![z]!
  fee i j k == fee i k j && fee i j k+fee j i k+fee k i j ≤ 0

def joint := #[375808,420352,390280,375296,464576,450448,553600]
def thirdMin := #[37952,44224,40316,37952,49608,47472,59648]

/-- The two outside colors fail on these many groupings. Any third matching
shares at least the displayed number, which excludes those from the prefix. -/
def minimumThird (v : Counts) (a b : Matching) (target depth left : Nat) (es : Array Nat) : Bool := Id.run do
  match depth with
  | 0 => return tripleCount v es ≥ target
  | d+1 =>
    let x := (low left).log2
    let mut ys := dropLow left
    for _ in [:15] do
      if ys == 0 then break
      let y := (low ys).log2
      ys := dropLow ys
      if a[x]! != y && b[x]! != y then
        let e := bit x ||| bit y
        if !minimumThird v a b target d (left ^^^ e) (es.push e) then return false
    return true

def outsideAudit (i : Nat) := Id.run do
  let (a,b) := canonical prices[i]!.row.cycles
  let v := counts false a b
  return v.both == joint[i]! && minimumThird v a b thirdMin[i]! 8 65535 #[]
end LastTwo
