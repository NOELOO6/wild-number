import ThreeStars
namespace ThreeStars
/- A column name is the color of its line to the root. This makes row 3
the identity in each local four-by-four table. -/
def four := List.range 4
def dig (p j : Nat) := (p >>> (2*j))%4
def names := (List.range 256).filter (fun p => (four.map (dig p)).eraseDups.length==4)
def triplesFrom {α} (xs : List α) := xs.flatMap fun a => xs.flatMap fun b => xs.map (fun c => #[a,b,c])
def cell (rows : Array Nat) (i j : Nat) := if i==3 then j else dig rows[i]! j
def localTables := (triplesFrom names).filter (fun r =>
  four.all (fun j => (four.map (cell r · j)).eraseDups.length==4))
def normal (t i j : Nat) :=
  if t==3 then j ^^^ (i ^^^ 3) else
    (j + (if i==3 then 0 else if i==t then 2 else if i==(if t==0 then 1 else 0) then 1 else 3))%4
def asNormal (r : Array Nat) (t : Nat) (p : Nat) :=
  four.all (fun i => four.all fun j => dig p (cell r i j)==normal t i (dig p j))
theorem local_types : names.length=24 ∧ localTables.length=24 ∧
    (localTables.all fun r => four.any fun t => names.any (asNormal r t))=true := by native_decide

def threePerm := names.filter (fun q => dig q 3==3)
def permFits (t : Nat) (k : K) (box rowOrder : Nat) := names.any fun q =>
  four.all (fun i => four.all (fun j =>
    dig q (normal t i j)==rule k box (dig rowOrder i) (dig q j)))
def partTypes (r : Array Nat) (k : K) (p b : Nat) := (List.range 3).all fun j =>
  permFits r[j]! k (dig b j) p
theorem seven_types : ((triplesFrom four).all fun r =>
    (List.finRange 7).any fun k => threePerm.any fun p => threePerm.any (partTypes r k p))=true := by native_decide
/-- A full coloring extending each of the seven star patterns. -/
def extension (k : K) (c : VertexRedraw.C) (v : VertexRedraw.V) : VertexRedraw.V :=
  let color := c.val
  let x := v.val
  let b := color/4
  let j := color%4
  Fin.ofNat' 16 (if color≥12 then x ^^^ (3 ^^^ j)
    else if x≥12 then 4*b + rule k b (x%4) j
    else if x/4==b then 12 + four.findIdx (fun i => rule k b i j==x%4)
    else 4*(3-b-x/4)+((x%4) ^^^ j))
theorem inhabited_patterns : ∀ k : K,
    (∀ c x, extension k c (extension k c x)=x ∧ extension k c x≠x) ∧
    (∀ c d x, extension k c x=extension k d x → c=d) ∧
    (∀ c, (required k c).all (fun e => extension k c e.1==e.2)=true) := by native_decide
#print axioms seven_types
end ThreeStars
