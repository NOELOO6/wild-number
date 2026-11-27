import CoreRange
namespace WildCuts.OneExtra.CoreTest
open Finset WildExact WildDeletion EdgeWalk

def first (n r : Nat) := (univ : Finset (Fin n)).filter fun x => x.val<r
def points (n mask : Nat) := (univ : Finset (Fin n)).filter fun x => mask.testBit x.val
def candidates {n : Nat} (R : Finset (Fin n)) := R.powerset.filter fun A => 3≤A.card ∧ 3≤(R\A).card
def splits (n r : Nat) := candidates (first n r)

def exteriorEdges (n r : Nat) : List (Edge n) := (List.finRange n).flatMap fun x =>
  if r≤x.val ∧ (x.val-r)%3=0 then ((List.finRange n).filter
    (fun y => decide (x.val<y.val ∧ y.val≤x.val+2))).map (x,·) else []

private def starList {n : Nat} (l : List (Fin n)) : List (Edge n) :=
  match l with
  | [] => []
  | a::tail => tail.map (fun b => (min a b,max a b))

/-- Draw two core stars and all exterior triples, then exchange one named
core vertex with a vertex of one exterior triple. -/
def redraw (n r mask l h : Nat) : List (Edge n) :=
  let xs := (List.finRange n).filter (fun x => decide (x.val<r))
  let old := exteriorEdges n r ++ starList (xs.filter (fun x => mask.testBit x.val)) ++
    starList (xs.filter (fun x => !(mask.testBit x.val)))
  if hl : l<n then if hh : h<n then
    let p := Equiv.swap (⟨l,hl⟩ : Fin n) ⟨h,hh⟩
    old.map (fun e => (min (p e.1) (p e.2),max (p e.1) (p e.2)))
  else old else old

def colored {n k : Nat} (g : Coloring n k) (c : Fin k) : List (Edge n) := (List.finRange n).flatMap fun x =>
  ((List.finRange n).filter fun y => decide (x<y ∧ g.paint x y=c)).map fun y => (x,y)

private theorem color_step {n k : Nat} (g : Coloring n k) (c : Fin k) {x y : Fin n} (h : (x,y)∈colored g c) :
    x≠y ∧ g.paint x y=c := by
  obtain ⟨a,_,b,hb,eq⟩ := (by simpa only [colored,List.mem_flatMap,List.mem_map] using h :
    ∃ a∈List.finRange n,∃ b∈(List.finRange n).filter (fun z => decide (a<z ∧ g.paint a z=c)),(a,b)=(x,y))
  cases eq
  obtain ⟨lt,clr⟩ := of_decide_eq_true (List.mem_filter.mp hb).2
  exact ⟨lt.ne,clr⟩

theorem to_graph {n k} (g : Coloring n k) (w : List (Edge n)) (c : Fin k) {x y}
    (h : Walk (Adj (w++colored g c)) x y) : Walk (Joined g w.toFinset c) x y := by
  have f {u v : Fin n} (e : (u,v)∈w++colored g c) : Joined g w.toFinset c u v := by
    rcases List.mem_append.mp e with e|e
    · exact Or.inl (Or.inl (List.mem_toFinset.mpr e))
    · exact Or.inr (color_step g c e)
  exact Walk.mapInto id (fun _ _ hit => .step (.stay _) (hit.elim f (fun e => joined_symm g (f e)))) h

theorem reaches {n k : Nat} (g : Coloring n k) (w : List (Edge n)) (R : Finset (Fin n))
    (checks : ∀ c (x : Fin n),∃ y∈R,(run (w++colored g c) n (2^x.val)).testBit y.val=true) :
    MeetsCore g w.toFinset R := by
  intro c x
  obtain ⟨y,hy,yes⟩ := checks c x
  exact ⟨y,hy,to_graph g w c (walk_of_seen x y _ yes)⟩

theorem winner {n : Nat} (g : Coloring n n) (hn : 3≤n) (w : List (Edge n))
    (leg : ∀ e∈w.toFinset,e.1<e.2) (cost : w.toFinset.card≤(2*n+2)/3)
    (paths : ∀ c,passes ⟨0,by omega⟩ (w++colored g c)=true) : Exact g ((2*n+2)/3) := by
  apply exact_of_upper ⟨w.toFinset,leg,cost,fun c x y => to_graph g w c (connected_of_passes _ _ (paths c) x y)⟩
  exact fun _ => odd_lower hn g

theorem no_split {n k} (g : Coloring n k) (outside : List (Edge n)) (R : Finset (Fin n))
    (cuts : List (Fin k × Nat))
    (checked : ∀ w∈cuts, let S := points n w.2
      S.Nonempty ∧ (∃ x : Fin n,x∉S) ∧ (∀ e∈outside,(e.1∈S ↔ e.2∈S)) ∧
      ∀ x y : Fin n,x≠y → g.paint x y=w.1 → (x∈S ↔ y∈S))
    (all : ∀ T : ↥(candidates R),∃ w∈cuts,R∩points n w.2=T.val ∨ R\T.val=R∩points n w.2)
    (A : Finset (Fin n)) (hA : A∈candidates R) (w : Lines n)
    (within : ∀ e∈w,e∈outside ∨ (e.1∈A ∧ e.2∈A) ∨ (e.1∈R\A ∧ e.2∈R\A)) : ¬Works g w := by
  obtain ⟨j,hj,partition⟩ := all ⟨A,hA⟩
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩,out,col⟩ := checked j hj
  let S := points n j.2
  change R∩S=A ∨ R\A=R∩S at partition
  have sub : A⊆R := mem_powerset.mp (mem_filter.mp hA).1
  have stable {a b : Fin n} (edge : (a,b)∈w) : a∈S ↔ b∈S := by
    rcases within _ edge with e|both|both
    · exact out _ e
    · obtain ⟨ha,hb⟩ := both
      rcases partition with eq|eq
      · exact iff_of_true (mem_inter.mp (eq.symm ▸ ha)).2 (mem_inter.mp (eq.symm ▸ hb)).2
      · have off {v : Fin n} (hv : v∈A) (hit : v∈S) := (mem_sdiff.mp (eq.symm ▸ mem_inter.mpr ⟨sub hv,hit⟩)).2 hv
        exact iff_of_false (off ha) (off hb)
    · obtain ⟨ha,hb⟩ := both
      rcases partition with eq|eq
      · have off {v : Fin n} (hv : v∈R\A) (hit : v∈S) :=
          (mem_sdiff.mp hv).2 (eq ▸ mem_inter.mpr ⟨(mem_sdiff.mp hv).1,hit⟩)
        exact iff_of_false (off ha) (off hb)
      · exact iff_of_true (mem_inter.mp (eq ▸ ha)).2 (mem_inter.mp (eq ▸ hb)).2
  have stay {u v : Fin n} (h : Walk (Joined g w j.1) u v) : u∈S → v∈S := by
    induction h with
    | stay => exact id
    | step _ edge ih =>
      rcases edge with (e|e)|⟨ne,eq⟩
      · exact fun hu => (stable e).mp (ih hu)
      · exact fun hu => (stable e).mpr (ih hu)
      · exact fun hu => (col _ _ ne eq).mp (ih hu)
  exact fun wins => hy (stay (wins j.1 x y) hx)

end WildCuts.OneExtra.CoreTest
