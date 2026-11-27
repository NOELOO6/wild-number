import EdgeWalk

namespace WildExact
abbrev Row (n : Nat) := List (Fin (n+1) × Fin (n+1))

def enumerate {n} : Nat → List (Fin (n+1)) → List (Row n)
  | _, [] => [[]]
  | 0, _::_ => []
  | fuel+1, x::xs => xs.flatMap fun y =>
      (enumerate fuel (xs.filter (· != y))).map ((x,y)::·)

def Rows (n : Nat) := enumerate (n+1) (List.finRange (n+1))

/-- Delete the temporary point, retaining actual ordinary edges. -/
def eraseRoot {n} (m : Row n) : List (EdgeWalk.Edge n) := m.filterMap fun e =>
  if h : e.1.val<n ∧ e.2.val<n then some (⟨e.1,h.1⟩,⟨e.2,h.2⟩) else none

abbrev TestLines (n : Nat) := List (EdgeWalk.Edge n)
def passesRow {n} (r : Fin n) (w : TestLines n) (m : Row n) :=
  EdgeWalk.passes r (w ++ eraseRoot m)

def rowHas {n} (m : Row n) (e : Fin (n+1) × Fin (n+1)) :=
  m.contains e || m.contains (e.2,e.1)

def totalI {α} (xs : List α) (f : α → Int) : Int := (xs.map f).sum

abbrev Price (n : Nat) := (Fin (n+1) × Fin (n+1)) × Int
def fee {n} (ps : List (Price n)) (r : Row n) :=
  totalI ps (fun ⟨e,v⟩ => if rowHas r e then v else 0)

def atIndex (n i : Nat) [NeZero n] : Fin n := Fin.ofNat' n i

def chains [NeZero n] (gs : List (List Nat)) : TestLines n :=
  gs.flatMap fun group => (group.zip group.tail).map fun ⟨a,b⟩ => (atIndex n a,atIndex n b)

def chooseK {α} (k : Nat) (xs : List α) : List (List α) :=
  match k,xs with
  | 0,_ => [[]]
  | _+1,[] => []
  | k+1,x::ys => (chooseK k ys).map (x::·) ++ chooseK (k+1) ys

def clean [NeZero n] (r : Row n) :=
  let a := (atIndex n 0).castSucc
  let b := (atIndex n 1).castSucc
  let x := (atIndex n 2).castSucc
  let z := Fin.last n
  !((rowHas r (a,b) && rowHas r (x,z)) || (rowHas r (a,x) && rowHas r (b,z)) ||
    (rowHas r (b,x) && rowHas r (a,z)))

end WildExact
