import NineData
import Counting
import Std.Sat.CNF.Relabel

namespace WildExact.Nine
open Std.Sat
def Hits (b : Family) := ∀ a x y, hit a x y=true → b a=true ∨ b x=true ∨ b y=true
def Caps (b : Family) := ∀ l∈limits, (l.1.filter b).length ≤ l.2
inductive Gate where
  | count (xs : List Nat) (threshold : Nat)
  deriving DecidableEq, Inhabited
def atom (i : Nat) := Gate.count [i] 1
def value (b : Family) : Gate → Bool
  | .count xs k => decide (k ≤ (xs.filter b).length)

@[simp] theorem atom_value (b : Family) (i : Nat) : value b (atom i) = b i := by
  cases h : b i <;> simp [atom,value,h]

inductive Rule where
  | partition (a b c : Nat)
  | sum (xs : List Nat) (i j : Nat)
  | bound (xs : List Nat) (k : Nat)

def requireCount (xs : List Nat) (k : Nat) : CNF.Clause Gate :=
  if k=0 then [] else [(.count xs k,false)]

def clause : Rule → CNF.Clause Gate
  | .partition a b c => [(atom a,true),(atom b,true),(atom c,true)]
  | .sum xs i j =>
    let d := xs.length / 2
    requireCount (xs.take d) i ++ requireCount (xs.drop d) j ++ [(.count xs (i+j),true)]
  | .bound xs k => [(.count xs (k+1),false)]
def admissible : Rule → Bool
  | .partition a b c => hit a b c
  | .sum _ _ _ => true
  | .bound xs k => limits.contains (xs,k)

private theorem append_eval {α} (a : α → Bool) (l r : CNF.Clause α) :
    CNF.Clause.eval a (l++r) = (CNF.Clause.eval a l || CNF.Clause.eval a r) := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih,Bool.or_assoc]

private theorem req_value (b : Family) (xs : List Nat) (k : Nat) :
    CNF.Clause.eval (value b) (requireCount xs k) = decide ((xs.filter b).length < k) := by
  by_cases h : (xs.filter b).length < k
  · have z : k≠0 := by omega
    simp [requireCount,value,h,z,Nat.not_le.mpr h]
  · by_cases z : k=0 <;> simp [requireCount,value,z,h,Nat.le_of_not_gt h]

theorem rule_sound (b : Family) (hits : Hits b) (caps : Caps b)
    (r : Rule) (ok : admissible r=true) : CNF.Clause.eval (value b) (clause r)=true := by
  cases r with
  | partition a x y =>
    have h := hits a x y ok
    simpa [clause,Bool.or_eq_true,or_assoc] using h
  | sum xs i j =>
    have h := congrArg (fun l : List Nat => (l.filter b).length) (List.take_append_drop (xs.length/2) xs)
    simp only [List.filter_append,List.length_append] at h
    simp [clause,append_eval,req_value,value,Bool.or_eq_true]
    omega
  | bound xs k =>
    have h := caps (xs,k) (List.contains_iff_mem.mp ok)
    change (xs.filter b).length ≤ k at h
    simpa [clause,value] using Nat.lt_succ_of_le h
abbrev Program := List Gate × List Rule
def totalizer : Nat → List Nat → Nat → Program
  | 0,_,_ => ([],[])
  | fuel+1,xs,limit => Id.run do
    if xs.length ≤ 1 then return ([],[])
    let left := xs.take (xs.length/2)
    let right := xs.drop (xs.length/2)
    let l := totalizer fuel left limit
    let r := totalizer fuel right limit
    let top := min xs.length (limit+1)
    let out := (List.range top).map (fun t => Gate.count xs (t+1))
    let joins := (List.range (min left.length (limit+1)+1)).flatMap fun i =>
      ((List.range (min right.length (limit+1)+1)).filter (fun j => 1≤i+j && i+j≤top)).map (Rule.sum xs i)
    return (l.1++r.1++out,l.2++r.2++joins)

def countProgram (l : List Nat × Nat) : Program := Id.run do
  if l.1.length ≤ l.2 then return ([],[])
  let (g,r) := totalizer 9 l.1 l.2
  return (g,r++[.bound l.1 l.2])

def partitions : List Rule := ids.flatMap fun a => ids.flatMap fun b =>
  (ids.filter (hit a b ·)).map (.partition a b ·)
def programs := limits.map countProgram
def gates := ((ids.map atom) ++ programs.flatMap Prod.fst).toArray
def rules := partitions ++ programs.flatMap Prod.snd
end WildExact.Nine
