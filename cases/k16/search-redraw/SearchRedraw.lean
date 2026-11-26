import SearchExample
import EdgeWalk
namespace SearchRedraw
open EdgeWalk WildDeletion
abbrev Raw := List (Nat × Nat)
abbrev Edges := List (Edge 15)
def points := List.range 16
def idEdge (x y : Nat) := y*(y-1)/2+x

def name (x y : Nat) := SearchExample.rows.findIdx (fun m => m[x]! == y)
def erase (m : Raw) : Edges := m.filterMap fun (a,b) =>
  if h : a<15 ∧ b<15 then some (⟨a,h.1⟩,⟨b,h.2⟩) else none
def mkKey (m : Raw) := m.foldl (fun v (x,y) => v ||| 2^(idEdge x y)) 0
def original (m : Array Nat) : Raw := points.filterMap fun x =>
  if x < m[x]! then some (x,m[x]!) else none
def old := SearchExample.rows.map (fun m => erase (original m))

structure Item where
  key : Nat
  edges : Edges
  deriving Inhabited
def item (m : Raw) : Item := ⟨mkKey m,erase m⟩
def select (mask : Nat) : Nat → List Nat → List Raw
  | _,[] => [[]]
  | 0,_::_ => []
  | d+1,x::xs => xs.flatMap fun y =>
    if mask.testBit (name x y) then ((select mask d (xs.erase y)).map ((x,y) :: ·)) else []
inductive Allowed (mask : Nat) : List Nat → Raw → Prop where
  | nil : Allowed mask [] []
  | pair {x y xs m} (present : y∈xs) (ok : mask.testBit (name x y) = true)
      (tail : Allowed mask (xs.erase y) m) : Allowed mask (x::xs) ((x,y)::m)
theorem exhaustive {mask xs m} (h : Allowed mask xs m) (d : Nat) (hd : m.length ≤ d) :
    m ∈ select mask d xs := by
  induction h generalizing d with
  | nil => cases d <;> simp [select]
  | @pair x y xs t mem ok _ ih =>
    cases d with
    | zero => simp at hd
    | succ d => exact List.mem_flatMap.mpr ⟨y,mem,by simp [ok,ih d (by simpa using hd)]⟩

def pool (mask : Nat) := (select mask 8 points).map item
def chains : List Nat → Raw
  | a::b::c::xs => (a,b)::(b,c)::chains xs
  | _ => []
def lines (s : String) := (s.splitOn "\n").filter (· != "")
def layouts := ((lines (include_str "layouts.txt")).map
  (fun s => erase (chains (s.toList.map (fun c => c.toNat-97))))).toArray
def wild (i : Nat) := layouts[i]!
def base (i : Nat) := let w := wild i
  decide (w.length=10 ∧ w.Nodup ∧ ∀ e∈w, e.1<e.2) && old.all (fun m => passes 0 (w++m))
def broken (ms : List Item) (i : Nat) := ms.filter (fun m => !passes 0 (wild i++m.edges))
def compatible (a b : Item) := a.key == b.key || (a.key &&& b.key) == 0
structure Plan where
  mask : Nat
  pivot : Nat
  ids : List Nat
  deriving Inhabited
@[noinline] def parse (s : String) := (lines s).map fun l => (l.splitOn " ").map String.toNat!
def plans := (parse (include_str "plans.txt")).map fun xs =>
  let e := xs[1]!
  let lo := (e ^^^ (e &&& (e-1))).log2
  let pivot := if e==0 then 0 else 1+idEdge lo e.log2
  Plan.mk xs[0]! pivot (xs.drop 2)
def anchors (p : Plan) (ms : List Item) := ms.filter (fun m => m.key.testBit (p.pivot-1))
def permitted (as' bad : List Item) (ids : List Nat) (i : Nat) :=
  (as'.zip ids).all (fun (a,j) => j != i || bad.all (fun b => !compatible a b))
def ok (p : Plan) :=
  let ms := pool p.mask
  if p.pivot==0 then
    let i := p.ids.headD 0
    base i && (broken ms i).isEmpty
  else
    let as' := anchors p ms
    !as'.isEmpty && as'.length == p.ids.length && p.ids.eraseDups.all (fun i =>
      base i && permitted as' (broken ms i) p.ids i)

def symmetries := (parse (include_str "symmetries.txt")).map List.toArray
def validSym (p : Array Nat) :=
  (p.extract 0 16).toList.mergeSort == points && p[15]! == 15 &&
  (p.extract 16 31).toList.mergeSort == List.range 15 &&
  points.all fun x => (List.range x).all fun y => name p[y]! p[x]! == p[16+name y x]!
def move (p : Array Nat) (m : Nat) := (List.range 15).foldl
  (fun a c => if m.testBit c then a ||| 2^p[16+c]! else a) 0
def symCover := Id.run do
  let mut haveMask := Array.replicate 32768 false
  for p in plans do haveMask := haveMask.set! p.mask true
  return symmetries.all validSym && (List.range 32768).all (fun m =>
    ((List.range 15).filter m.testBit).length != 6 || symmetries.any (fun p => haveMask[move p m]!))
end SearchRedraw
