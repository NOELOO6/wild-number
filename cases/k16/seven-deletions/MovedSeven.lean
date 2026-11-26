import Seven
namespace MovedSeven
set_option maxHeartbeats 0
set_option maxRecDepth 200000
def groups := ((include_str "groupings.txt").trim.splitOn "\n").map fun l =>
  (l.splitOn " ").filterMap String.toNat?
def pts := List.range 16
def bit (i : Nat) := 1 <<< i
def valid (g : List Nat) := g.length == 5 &&
  g.all (fun s => s < 65536 && (pts.filter s.testBit).length == 3) &&
  g.foldl (· ||| ·) 0 == 65534
def rotate (s d : Nat) := pts.foldl (fun m v =>
  if s.testBit v then m ||| bit (Seven.rot v d) else m) 0
def cuts (g : List Nat) := g.map (· ||| 1) ++
  (g.zipIdx.flatMap (fun (s,i) => (g.take i).map (s ||| ·)))
def turns : Array Nat := Id.run do
  let mut a := Array.replicate 65536 0
  for (g,i) in groups.zipIdx do
    for s in cuts g do
      for d in [:7] do
        a := a.modify (rotate s d) (· ||| bit i)
  return a
def full := bit groups.length - 1
def passes (m : Array Nat) : Nat := Id.run do
  let mut bad := 0
  for i in [0:m.size] do
    for j in [0:i] do
      let s := m[i]! ||| m[j]!
      bad := bad ||| turns[s]!
      for k in [0:j] do bad := bad ||| turns[s ||| m[k]!]!
  return full ^^^ bad
def starter (base : Seven.Base) (v : Nat) : Array Nat := Id.run do
  let mut edges := #[bit v ||| bit 15]
  for j in [0:15] do
    for i in [0:j] do
      if base.edges.testBit (Seven.idx i j) then edges := edges.push (bit i ||| bit j)
  return edges
def fixed := (Array.range 7).map (fun i => bit i ||| bit (7+i)) |>.push (bit 14 ||| bit 15)
def entries (v : Nat) := (Seven.bases v).map (fun b => (b.tag,passes (starter b v)))
def buckets := (entries 7).foldl (fun (a : Array (List Nat)) (t,p) =>
  a.modify t (p :: ·)) (Array.replicate 65536 [])
theorem every_moving_deletion :
    groups.length = 73 ∧ groups.all valid = true ∧ passes fixed = full ∧
    ((entries 0).map (fun (t,_) => buckets[65535 ^^^ t]!.length)).sum = 797448 ∧
    (entries 0).all (fun (t,p) => buckets[65535 ^^^ t]!.all
      (fun q => p &&& q != 0)) = true := by native_decide
#print axioms every_moving_deletion
end MovedSeven
