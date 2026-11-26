import EdgeWalk
namespace Paired
open EdgeWalk WildDeletion
abbrev V := Fin 15
abbrev Edges := List (Edge 15)
abbrev P := Fin 105
abbrev C := P × Fin 16
abbrev K := Fin 3
abbrev Schedule := List (Nat × Edges)

def lines (doc : String) := (doc.splitOn "\n").filter (· != "")
def words (s : String) := (s.splitOn " ").filter (· != "")
def nums (s : String) := (words s.trim).map String.toNat!
def projections := ((lines (include_str "projections.txt")).map (fun s =>
  (s.toList.map (fun c => c.toNat - '0'.toNat)).toArray)).toArray

def pairs (p : P) : List (Nat × Nat) := (List.range 8).filterMap fun a =>
  let b := projections[p.val]![a]!
  if a < b then some (a,b) else none

def idEdge (a b : Nat) := let hi := max a b; hi*(hi-1)/2 + min a b
def pairIds (p : P) := (pairs p).map fun (a,b) => idEdge a b

def restrictEdge (a b : Nat) : Edges :=
  if ha : a < 15 then if hb : b < 15 then [(⟨a,ha⟩,⟨b,hb⟩)] else [] else []
def color (c : C) : Edges := ((pairs c.1).zipIdx).flatMap fun ((a,b),i) =>
  let t := (c.2.val.testBit i).toNat
  restrictEdge (2*a) (2*b+t) ++ restrictEdge (2*a+1) (2*b+(1-t))
def anchor : Edges := (List.range 8).flatMap fun a => restrictEdge (2*a) (2*a+1)

def chains : List Nat → Edges
  | a::b::c::rest => restrictEdge a b ++ restrictEdge b c ++ chains rest
  | _ => []
def parseSchedule (doc : String) : Schedule := (lines doc).map fun line =>
  let ws := words line
  (ws[0]!.toNat!, chains (ws[1]!.toList.map fun c => c.toNat-'a'.toNat))
def schedules : Array Schedule := #[parseSchedule (include_str "layouts0.txt"),
  parseSchedule (include_str "layouts1.txt"), parseSchedule (include_str "layouts2.txt")]
def prices : Array (Array Nat) := #[(nums (include_str "prices0.txt")).toArray,
  (nums (include_str "prices1.txt")).toArray, (nums (include_str "prices2.txt")).toArray]
def special (k : K) : P := if k.val == 0 then 0 else if k.val == 1 then 3 else 18
def sched (k : K) := schedules[k.val]!
def price (k : K) (e : Nat) := prices[k.val]![e]!
def charge (k : K) (p : P) := ((pairIds p).map (price k)).sum

def failure (w m : Edges) : Nat := if passes 0 (w ++ m) then 0 else 1
def cost (ls : Schedule) (m : Edges) := (ls.map fun (w,g) => w * failure g m).sum
def weight (ls : Schedule) := (ls.map Prod.fst).sum
def cap (k : K) (p : P) := ((List.finRange 16).map fun s => cost (sched k) (color (p,s))).foldl max 0
def residual (k : K) := (pairIds 0 ++ pairIds (special k)).foldl List.erase ((List.range 28) ++ (List.range 28))
end Paired
