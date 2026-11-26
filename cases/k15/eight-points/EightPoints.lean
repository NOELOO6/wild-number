import EdgeWalk
namespace EightPoints
open EdgeWalk WildDeletion
abbrev Raw := List (Nat × Nat)
abbrev Edges := List (Edge 15)
def draw (a b : Nat) : Edges := if ha : a < 15 then if hb : b < 15 then
  [(⟨a,ha⟩,⟨b,hb⟩)] else [] else []
def withoutRoot (m : Raw) : Edges := m.flatMap (fun (a,b) => draw a b)
def chain : List Nat → Edges
  | a::b::c::_ => draw a b ++ draw b c
  | _ => []
def loose := List.range' 8 7
def layouts : List Edges := loose.flatMap fun z =>
  let xs := loose.erase z
  xs.tail.flatMap fun a => xs.tail.filterMap fun b =>
    if a < b then
      let t := [xs.head!,a,b]
      some ([ [0,1,2],[3,4,5],[6,7,z],t, xs.filter (fun v => !t.contains v)].flatMap chain)
    else none

def known (v : Nat) := v < 8 || v == 15
def freeVertices (p : Raw) := (List.range 16).filter fun v =>
  !(p.any (fun (a,b) => a == v || b == v))
def fill : Nat → List Nat → List Raw
  | _, [] => [[]]
  | 0, _::_ => []
  | n+1, a::xs => xs.flatMap fun b => if known a && known b then [] else
      (fill n (xs.erase b)).map ((a,b) :: ·)
def completions (p : Raw) := (fill 8 (freeVertices p)).map (p ++ ·)

inductive Fills : List Nat → Raw → Prop where
  | nil : Fills [] []
  | pair {a b xs t} (hb : b ∈ xs) (free : (known a && known b) = false)
      (next : Fills (xs.erase b) t) : Fills (a::xs) ((a,b)::t)
theorem every_fill {xs m} (h : Fills xs m) (fuel : Nat) (bound : m.length ≤ fuel) :
    m ∈ fill fuel xs := by
  induction h generalizing fuel with
  | nil => cases fuel <;> simp [fill]
  | @pair a b xs t hb hfree _ ih =>
    cases fuel with
    | zero => simp at bound
    | succ n => exact List.mem_flatMap.mpr ⟨b,hb,by simp [hfree,ih n (by simpa using bound)]⟩

def safe (m : Raw) (w : Edges) := passes 0 (w ++ withoutRoot m)
def failures (m : Raw) := (layouts.filter fun w => !(safe m w)).length
def ceiling : List Nat → Nat
  | [] => 0
  | n::ns => max n (ceiling ns)
def cost (p : Raw) := ceiling ((completions p).map failures)
def working (cs : List (Raw × Raw)) (w : Edges) := cs.all (fun (_,m) => safe m w)
def surviving (cs : List (Raw × Raw)) := layouts.filter (working cs)
def spent (cs : List (Raw × Raw)) := (cs.map fun c => cost c.1).sum

def parseEdges : List Nat → Raw
  | a::b::rest => (a,b)::parseEdges rest
  | _ => []
def patterns := (((include_str "local-table.txt").splitOn "\n").filter (· != "")).map fun l =>
  parseEdges ((l.splitOn " ").map String.toNat!)
end EightPoints
