import Prescribed
namespace WildTwelve
open Prescribed
set_option maxRecDepth 200000

def scale : Nat := 1000000
structure Tangent where
  row : Prices
  intercept : Array Nat
  slope : Array Nat
  valid : Bool
  weighted : Nat
  deriving Inhabited

def readRows : Array Tangent := Id.run do
  let lines := (((include_str "tangent-prices.txt").trim.splitOn "\n").toArray.map
    (fun line => (line.splitOn " ").toArray.map String.toInt!))
  return (Array.range 11).map fun i => Id.run do
    let pos := i*17
    let h := lines[pos+1]!
    let r : Prices := ⟨lines[pos]!.map Int.toNat,0,h[0]!,h[1]!,h[2]!,lines[pos+2]!,lines.extract (pos+3) (pos+14)⟩
    let keys := lines[pos+14]!
    let mut aa := Array.replicate 6000 0
    let mut bb := aa
    let mut ok := true
    for j in [:keys.size] do
      let a := lines[pos+15]![j]!.toNat
      let b := lines[pos+16]![j]!.toNat
      for m in [2:13] do
        if m*a > 2*scale + m*(m-2)*b then ok := false
      aa := aa.set! keys[j]!.toNat a
      bb := bb.set! keys[j]!.toNat b
    return ⟨r,aa,bb,ok,h[3]!.toNat⟩

def internal (m : Matching) := (Array.range 65536).map fun s => Id.run do
  for x in [:16] do
    if s.testBit x && s.testBit m[x]! then return 1
  return 0

def signature (gs : Array Nat) (ca cb : Array Bool) (ia ib : Array Nat) := Id.run do
  let mut na := 0
  let mut nb := 0
  let mut ra := false
  let mut rb := false
  let mut common := 0
  let mut wa := 0
  let mut wb := 0
  for i in [1:6] do
    wa := wa+ia[gs[i]!]!
    wb := wb+ib[gs[i]!]!
    for j in [:i] do
      let s := gs[i]! ||| gs[j]!
      if ca[s]! then
        na := na+1
        if j == 0 then ra := true
      if cb[s]! then
        nb := nb+1
        if j == 0 then rb := true
      if ca[s]! && cb[s]! then common := common+1
  let u := wa*6+ra.toNat+2*(na==3).toNat
  let v := wb*6+rb.toNat+2*(nb==3).toNat
  return 4*(40*min u v+max u v)+common

def layouts (row : Tangent) (ca cb : Array Bool) (ia ib : Array Nat) (depth left : Nat) (gs : Array Nat)
    (badA badB : Bool) (v : Counts) : Counts := Id.run do
  match depth with
  | 0 =>
    if !badA then return v
    let v := {v with one := v.one+1}
    if !badB then return v
    let h := signature gs ca cb ia ib
    return depositWeighted gs row.intercept[h]! row.slope[h]! v
  | n+1 =>
    let x := low left
    let mut second := dropLow left
    let mut w := v
    for _ in [:14] do
      if second == 0 then break
      let y := low second
      second := dropLow second
      let mut third := second
      for _ in [:13] do
        if third == 0 then break
        let s := x ||| y ||| low third
        third := dropLow third
        let ba := badA || gs.any (fun t => ca[s ||| t]!)
        let bb := badB || gs.any (fun t => cb[s ||| t]!)
        w := layouts row ca cb ia ib n (left ^^^ s) (gs.push s) ba bb w
    return w

def check (i : Nat) := Id.run do
  let r := readRows[i]!
  let row := r.row
  let (a,b) := canonical row.cycles
  let init : Counts := ⟨0,0,Array.replicate 65536 0,Array.replicate (1820*8008) 0⟩
  let ct := layouts r (closed a) (closed b) (internal a) (internal b)
    5 32767 #[32768] false false init
  let mut price : Int := 0
  for y in [:16] do
    for x in [:y] do
      if a[x]! != y && b[x]! != y then price := price+row.edge[pairId x y]!
  let gain := (ct.both : Int)-price-10*row.selected-3*row.omitted
  let table := keyTable (readRows.map Tangent.row)
  return r.valid && ct.one == 191800 && ct.both == r.weighted && gain == row.gain &&
    row.gain ≥ 13652153205 && eachThird true table row ct a b 8 65535 (Array.replicate 16 0) #[] 0 1 == (expected true)[i]!

def transfersOK := (Array.range 11).all fun i => (Array.range 11).all fun j => (Array.range 11).all fun k =>
  let fee := fun x y z : Nat => readRows[x]!.row.transfer[y]![z]!
  fee i j k == fee i k j && fee i j k+fee j i k+fee k i j ≤ 0
end WildTwelve
