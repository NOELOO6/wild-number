import EdgeWalk
namespace SixColors
open EdgeWalk WildDeletion
abbrev Edges := List (Edge 15)
abbrev Raw := List (Nat × Nat)
def oldName (a b : Nat) := if b == 15 then a else (8*(a+b))%15
def edgeId (a b : Nat) := b*(b-1)/2+a
def bits (es : Raw) := es.foldl (fun t e => t ||| 2^(edgeId e.1 e.2)) 0
def select : Nat → List Nat → Nat → List Raw
  | _, [], _ => [[]]
  | 0, _::_, _ => []
  | d+1, a::xs, mask => xs.flatMap fun b => if mask.testBit (oldName a b) then
      (select d (xs.erase b) mask).map ((a,b) :: ·) else []

inductive Allowed (mask : Nat) : List Nat → Raw → Prop where
  | nil : Allowed mask [] []
  | pair {a b xs t} (present : b ∈ xs) (ok : mask.testBit (oldName a b) = true)
      (tail : Allowed mask (xs.erase b) t) : Allowed mask (a::xs) ((a,b)::t)

theorem all_matchings {mask xs m} (h : Allowed mask xs m) (d : Nat) (hd : m.length ≤ d) :
    m ∈ select d xs mask := by
  induction h generalizing d with
  | nil => cases d <;> simp [select]
  | @pair a b xs t hb hc _ ih =>
    cases d with
    | zero => simp at hd
    | succ d => exact List.mem_flatMap.mpr ⟨b,hb,by simp [hc,ih d (by simpa using hd)]⟩

def point (r x : Nat) : Option (Fin 15) :=
  if x == r then none else let v := if x < r then x else x-1
                           if h : v < 15 then some ⟨v,h⟩ else none
def erasePoint (r : Nat) (es : Raw) : Edges := es.filterMap fun (a,b) => do
  return (← point r a, ← point r b)
structure Item where
  key : Nat
  edges : Edges
  deriving Inhabited
def item (r : Nat) (m : Raw) := Item.mk (bits m) (erasePoint r m)
def pool (r mask : Nat) := (select 8 (List.range 16) mask).map (item r)
def original (c : Nat) : Raw := (List.range 16).flatMap fun b =>
  (List.range b).filterMap fun a => if oldName a b == c then some (a,b) else none
def originals (r : Nat) := (List.range 15).map fun c => erasePoint r (original c)

def lines (s : String) := (s.splitOn "\n").filter (· != "")
def rawLayouts := ((lines (include_str "layouts.txt")).map (fun s => s.toList.map (fun c => c.toNat-97))).toArray
def chains : List Nat → Raw
  | a::b::c::xs => (a,b)::(b,c)::chains xs
  | _ => []
def wild (r i : Nat) := erasePoint r (chains (rawLayouts[i]?.getD []))
structure Plan where
  root : Nat
  mask : Nat
  pivot : Nat -- zero for a common witness, otherwise one plus the edge index
  ids : List Nat
  deriving Inhabited
def plans := (lines (include_str "six.txt")).map fun s =>
  let xs := (s.splitOn " ").map String.toNat!
  Plan.mk xs[0]! xs[1]! xs[2]! (xs.drop 3)
def active (p : Plan) (ms : List Item) := ms.filter fun m => m.key.testBit (p.pivot-1)
def compatible (a b : Item) := a.key == b.key || (a.key &&& b.key) == 0
def baseOK (r : Nat) (w : Edges) := w.length == 10 && (originals r).all (fun m => passes 0 (w++m))
def works (p : Plan) (ms : List Item) (i : Nat) :=
  let w := wild p.root i
  baseOK p.root w && ms.all (fun m => passes 0 (w++m.edges))
def rowOK (p : Plan) :=
  let ms := pool p.root p.mask
  if p.pivot == 0 then works p ms (p.ids.headD 0) else
    let candidates := active p ms
    !candidates.isEmpty && candidates.length == p.ids.length &&
    (candidates.zip p.ids).all fun (a,i) => works p (ms.filter (compatible a)) i
def units : List Nat := [1,2,4,7,8,11,13,14]
def imageMask (m a b : Nat) := (List.range 15).foldl (fun t c =>
  if m.testBit c then t ||| 2^((a*c+b)%15) else t) 0
def images (root m : Nat) := units.flatMap fun a =>
  (if root == 15 then List.range 15 else [0]).map fun b => imageMask m a b
def size (m : Nat) := ((List.range 15).filter m.testBit).length
def canonical (r m : Nat) := (images r m).all (m ≤ ·)
end SixColors
