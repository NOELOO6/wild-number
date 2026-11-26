import Anchors
namespace WildExact
open Finset WildDeletion
variable {n : Nat}

def chains [NeZero n] (gs : List (List Nat)) : TestLines n :=
  gs.flatMap fun group => (group.zip group.tail).map fun ⟨a,b⟩ => (atIndex n a,atIndex n b)

def chooseK {α} (k : Nat) (xs : List α) : List (List α) :=
  match k,xs with
  | 0,_ => [[]]
  | _+1,[] => []
  | k+1,x::ys => (chooseK k ys).map (x::·) ++ chooseK (k+1) ys

def finishes (n k : Nat) [NeZero n] : List (TestLines n) :=
  let rest := (List.range n).drop 3
  if k=0 then [chains [[0,1,2],rest]] else
  ((chooseK k rest).filter (·.contains 3)).map fun t =>
    chains [[0,1,2],t,rest.filter (!t.contains ·)]

def clean [NeZero n] (r : Row n) :=
  let a := (atIndex n 0).castSucc
  let b := (atIndex n 1).castSucc
  let x := (atIndex n 2).castSucc
  let z := Fin.last n
  !((rowHas r (a,b) && rowHas r (x,z)) || (rowHas r (a,x) && rowHas r (b,z)) ||
    (rowHas r (b,x) && rowHas r (a,z)))

theorem clean_row [NeZero n] (hn : n%2=1) (g : Coloring n n)
    (good : GoodThree g (atIndex n 0) (atIndex n 1) (atIndex n 2))
    (room : 6≤n) (c : Fin n) (r : Row n) (mem : r∈Rows n)
    (res : Respects (mate (augment hn g) c) r) : clean r = true := by
  let a := atIndex n 0
  let b := atIndex n 1
  let x := atIndex n 2
  have vals : a.val=0 ∧ b.val=1 ∧ x.val=2 :=
    ⟨Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)⟩
  have ab : a≠b := fun h => by have := congrArg Fin.val h; omega
  have ax : a≠x := fun h => by have := congrArg Fin.val h; omega
  have bx : b≠x := fun h => by have := congrArg Fin.val h; omega
  have ord (i j : Fin n) (ne : i≠j) :
      rowHas r (i.castSucc,j.castSucc) = decide (g.paint i j=c) := by
    rw [row_equiv _ c r mem res _ _ (fun h => ne (Fin.castSucc_injective _ h)),augment_paint]
  have star (i : Fin n) : rowHas r (i.castSucc,Fin.last n) = decide (missingColor g i=c) := by
    rw [row_equiv _ c r mem res _ _ (Fin.ne_of_lt (Fin.castSucc_lt_last _))]
    simp [augment]
  change (!((rowHas r (a.castSucc,b.castSucc) && rowHas r (x.castSucc,Fin.last n)) ||
    (rowHas r (a.castSucc,x.castSucc) && rowHas r (b.castSucc,Fin.last n)) ||
    (rowHas r (b.castSucc,x.castSucc) && rowHas r (a.castSucc,Fin.last n))))=true
  simp only [ord a b ab,ord a x ax,ord b x bx,star,Bool.not_eq_true',Bool.or_eq_false_iff,
    Bool.and_eq_false_imp,decide_eq_true_eq,decide_eq_false_iff_not]
  obtain ⟨ga,gb,gx⟩ := good
  exact ⟨⟨fun u v => ga (u.trans v.symm), fun u v => gb (u.trans v.symm)⟩,fun u v => gx (u.trans v.symm)⟩

def nativeBounds [NeZero n] (layouts : List (TestLines n)) (base : Int) (price : List (Price n)) :=
  (Rows n).all fun m => !clean m || decide
    (totalI layouts (fun w => if passesRow (atIndex n 0) w m then 0 else 1) ≤ base + fee price m)

theorem finish_small [NeZero n] (hn : n%2=1) (room : 6≤n) (g : Coloring n n)
    (b : Nat) (layouts : List (TestLines n)) (base : Int) (price : List (Price n))
    (perRow : nativeBounds layouts base price=true)
    (leg : ∀ w∈layouts, w.length≤b ∧ ∀ e∈w, e.1<e.2)
    (noself : ∀ e∈price,e.1.1≠e.1.2)
    (slack : (n:Int)*base+totalI price Prod.snd < layouts.length) : Upper g b := by
  obtain ⟨p,good⟩ := normalize_three hn room g
  apply upper_back p g
  let g' := renamed p g
  obtain ⟨rs,hr⟩ := choose_rows (augment hn g')
  let cs := List.finRange n
  let f := fun w c => if passesRow (atIndex n 0) w (rs c) then (0:Int) else 1
  have bound (c) : totalI layouts (fun w => f w c) ≤ base + fee price (rs c) := by
    have test := List.all_eq_true.mp perRow _ (hr c).1
    have cl := clean_row hn g' good room c (rs c) (hr c).1 (hr c).2
    simpa [cl,f] using test
  have hi := total_mono cs (fun c _ => bound c)
  rw [total_add,total_const,fees_sum _ _ hr price noself] at hi
  have len : cs.length=n := List.length_finRange
  rw [len] at hi
  have lt : totalI layouts (fun w => totalI cs (f w)) < (layouts.length:Int)*1 := by
    rw [transpose,mul_one]
    exact lt_of_le_of_lt hi slack
  obtain ⟨w,mem,all⟩ := some_below layouts _ 1 lt
  apply from_rows hn g' rs (fun c => (hr c).2) (atIndex n 0) w b (leg w mem).1 (leg w mem).2
  intro c
  have eqB (t : Bool) : (if !t then (1:Int) else 0) = (if t then 0 else 1) := by cases t <;> decide
  have h := all_of_zero cs (fun j => !(passesRow (atIndex n 0) w (rs j))) (by
    simpa only [f,eqB] using all) c (List.mem_finRange c)
  simpa using h

def prices9 : List (Price 9) := [((0,1),1),((0,2),1),((1,2),1),
  ((3,9),1),((4,9),1),((5,9),1),((6,9),1),((7,9),1),((8,9),1)]
def prices11 : List (Price 11) := [((0,1),2),((0,2),2),((1,2),2),((0,11),2),((1,11),2),((2,11),2)]

set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem upper7 (g : Coloring 7 7) : Upper g 5 := by
  apply finish_small (by decide) (by decide) g 5 (finishes 7 0) 0 []
  all_goals native_decide
theorem upper9 (g : Coloring 9 9) : Upper g 6 := by
  apply finish_small (by decide) (by decide) g 6 (finishes 9 3) 0 prices9
  all_goals native_decide
theorem upper11 (g : Coloring 11 11) : Upper g 8 := by
  apply finish_small (by decide) (by decide) g 8 (finishes 11 4) 1 prices11
  all_goals native_decide

theorem chain_bound (n : Nat) [NeZero n] (g : Coloring n n) (b : Nat) (w : TestLines n)
    (short : w.length ≤ b) (legal : ∀ e∈w,e.1<e.2) (test : EdgeWalk.passes (atIndex n 0) w=true) :
    Upper g b := by
  refine ⟨w.toFinset,fun e h => legal e (List.mem_toFinset.mp h),(List.toFinset_card_le _).trans short,?_⟩
  intro c x y
  apply Walk.mapInto id _ (EdgeWalk.connected_of_passes _ _ test x y)
  intro a z h
  exact Walk.step (.stay _) (Or.inl (h.imp List.mem_toFinset.mpr List.mem_toFinset.mpr))

theorem upper3 (g : Coloring 3 3) : Upper g 2 :=
  chain_bound _ g _ (chains [[0,1,2]]) (by decide) (by decide) (by decide)
theorem upper5 (g : Coloring 5 5) : Upper g 4 :=
  chain_bound _ g _ (chains [[0,1,2,3,4]]) (by decide) (by decide) (by decide)

theorem K3_K4 : (∀ g : Coloring 3 3, Exact g 2) ∧
    (∀ g : Coloring 4 3, Exact g 2) := exact_pair (n:=3) (by decide) upper3
theorem K5_K6 : (∀ g : Coloring 5 5, Exact g 4) ∧
    (∀ g : Coloring 6 5, Exact g 4) := exact_pair (n:=5) (by decide) upper5
theorem K7_K8 : (∀ g : Coloring 7 7, Exact g 5) ∧
    (∀ g : Coloring 8 7, Exact g 5) := exact_pair (n:=7) (by decide) upper7
theorem K9_K10 : (∀ g : Coloring 9 9, Exact g 6) ∧
    (∀ g : Coloring 10 9, Exact g 6) := exact_pair (n:=9) (by decide) upper9
theorem K11_K12 : (∀ g : Coloring 11 11, Exact g 8) ∧
    (∀ g : Coloring 12 11, Exact g 8) := exact_pair (n:=11) (by decide) upper11
#print axioms K3_K4
#print axioms K5_K6
#print axioms K7_K8
#print axioms K9_K10
#print axioms K11_K12
end WildExact
