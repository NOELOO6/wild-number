import PaletteSizes
import SmallSides
import TwoCoreCheck

namespace WildSlots.Certificates
open Finset WildExact WildDeletion WildCuts.OneExtra

structure Setup (d r n k : Nat) where
  graph : Coloring n k
  fixed : List (EdgeWalk.Edge n)
  point : Fin d → Fin n
  dest : Fin d → Fin n
  root : Fin n
  key : Fin r ↪ Fin k

variable {d r n k : Nat}

def edges (t : Setup d r n k) (p : Perm (Fin d)) :=
  t.fixed ++ (List.finRange d).map (fun i => edge (t.point i) (t.dest (p i)))

theorem actual (t : Setup d r n k) (p : Perm (Fin d)) :
    (edges t p).toFinset=draw t.fixed.toFinset t.point t.dest p := by
  ext e
  simp [edges,draw]

def connects (t : Setup d r n k) (p : Perm (Fin d)) (c : Fin k) :=
  EdgeWalk.passes t.root (edges t p++CoreTest.colored t.graph c)

def sealed (t : Setup d r n k) (p : Perm (Fin d)) (c : Fin k) : Bool :=
  let w := edges t p
  let seen := (EdgeWalk.run (w++CoreTest.colored t.graph c) n (2^t.root.val)).testBit
  decide (seen t.root.val=true ∧ (∃ y : Fin n,seen y.val=false) ∧
    (∀ e∈w,seen e.1.val=seen e.2.val) ∧ ∀ x y : Fin n,x≠y → t.graph.paint x y=c → seen x.val=seen y.val)

theorem has_path (t : Setup d r n k) (p : Perm (Fin d)) (c : Fin k) (ok : connects t p c=true) :
    Connected (Joined t.graph (draw t.fixed.toFinset t.point t.dest p) c) := by
  rw [←actual]
  exact fun x y => CoreTest.to_graph _ _ _ (EdgeWalk.connected_of_passes _ _ ok x y)

theorem has_cut (t : Setup d r n k) (p : Perm (Fin d)) (c : Fin k) (ok : sealed t p c=true) :
    ¬Connected (Joined t.graph (draw t.fixed.toFinset t.point t.dest p) c) := by
  let w := edges t p
  let side (v : Fin n) := (EdgeWalk.run (w++CoreTest.colored t.graph c) n (2^t.root.val)).testBit v.val
  change decide (_ ∧ (∃ y : Fin n,side y=false) ∧ _ ∧ _)=true at ok
  obtain ⟨yes,⟨y,no⟩,wild,paint⟩ := of_decide_eq_true ok
  intro conn
  rw [←actual] at conn
  have equal := constant_on_walk (f:=side) (fun a b (e : Joined t.graph w.toFinset c a b) => by
    rcases e with (e|e)|⟨ne,clr⟩
    · exact wild _ (List.mem_toFinset.mp e)
    · exact (wild _ (List.mem_toFinset.mp e)).symm
    · exact paint _ _ ne clr) (conn t.root y)
  exact Bool.noConfusion (yes.symm.trans (equal.trans no))

/-- Two verified searches from named vertices cover the whole drawing. -/
def twoStarts (t : Setup d r n k) (p : Perm (Fin d)) (c : Fin k) : Bool :=
  let es := edges t p++CoreTest.colored t.graph c
  let first := (EdgeWalk.run es n (2^t.root.val)).testBit
  decide (∃ y : Fin n,∀ x : Fin n,first x.val=true ∨ (EdgeWalk.run es n (2^y.val)).testBit x.val=true)

private theorem from_two (t : Setup d r n k) (p : Perm (Fin d)) (c : Fin k) (ok : twoStarts t p c=true) :
    ∃ y,∀ x,let G := Joined t.graph (draw t.fixed.toFinset t.point t.dest p) c
      Walk G t.root x ∨ Walk G y x := by
  obtain ⟨y,all⟩ := of_decide_eq_true ok
  refine ⟨y,fun x => ?_⟩
  rw [←actual]
  exact (all x).imp (fun h => CoreTest.to_graph _ _ _ (EdgeWalk.walk_of_seen _ _ _ h))
    (fun h => CoreTest.to_graph _ _ _ (EdgeWalk.walk_of_seen _ _ _ h))

def palette (t : Setup d r n k) (S : Finset (Fin k)) :=
  ∃ p : Perm (Fin d),∀ c∈S,Connected (Joined t.graph (draw t.fixed.toFinset t.point t.dest p) c)

def target (t : Setup d r n k) := univ.map t.key
def near (t : Setup d r n k) (h : Fin r) := ∃ p : Perm (Fin d),
  let G := Joined t.graph (draw t.fixed.toFinset t.point t.dest p)
  (∀ c,c≠t.key h → Connected (G c)) ∧ ¬Connected (G (t.key h)) ∧
  ∃ y,∀ x,Walk (G (t.key h)) t.root x ∨ Walk (G (t.key h)) y x

def Sharp (t : Setup d r n k) (b : Nat) :=
  (∀ p : Perm (Fin d),let w := draw t.fixed.toFinset t.point t.dest p; Legal w ∧ w.card=b) ∧
  (∀ S : Finset (Fin k),S.card<r → palette t S) ∧ ¬palette t (target t) ∧ ∀ h,near t h

theorem from_checks (t : Setup d r n k) (b : Nat)
    (budget : ∀ p : Perm (Fin d),let w := (edges t p).toFinset; (∀ e∈w,e.1<e.2) ∧ w.card=b)
    (leave : ∀ h,∃ p : Perm (Fin d),(∀ c : Fin k,c≠t.key h → connects t p c=true) ∧ twoStarts t p (t.key h)=true)
    (stuck : ∀ p : Perm (Fin d),∃ h,sealed t p (t.key h)=true) : Sharp t b := by
  refine ⟨fun p => by simpa only [←actual,Legal] using budget p,?_,?_,?_⟩
  · intro S hs
    obtain ⟨h,off⟩ : ∃ h,t.key h∉S := by
      by_contra! allColors
      have sub : target t⊆S := by
        intro c hc
        obtain ⟨h,_,rfl⟩ := mem_map.mp hc
        exact allColors h
      have count : (target t).card=r := by simp [target]
      have le := card_le_card sub
      omega
    obtain ⟨p,good,_⟩ := leave h
    exact ⟨p,fun c hc => has_path t p c (good c (fun eq => off (eq ▸ hc)))⟩
  · rintro ⟨p,allColors⟩
    obtain ⟨h,bad⟩ := stuck p
    exact has_cut t p _ bad (allColors _ (mem_map.mpr ⟨h,mem_univ _,rfl⟩))

  · intro h
    obtain ⟨p,good,two⟩ := leave h
    obtain ⟨j,cut⟩ := stuck p
    have same : t.key j=t.key h := Classical.byContradiction (fun ne =>
      has_cut t p _ cut (has_path t p _ (good _ ne)))
    exact ⟨p,fun c ne => has_path t p _ (good c ne),same ▸ has_cut t p _ cut,from_two t p _ two⟩

/-- Temporary singleton tests let every other movable point use every other destination. -/
def oneList (t : Setup d r n k) (i j : Fin d) :=
  t.fixed ++ (List.finRange d).flatMap (fun a =>
    ((List.finRange d).filter (fun b => decide (a=i ↔ b=j))).map (fun b => (t.point a,t.dest b)))

def singleChecks (t : Setup d r n k) := ∀ i j c,
  EdgeWalk.passes t.root (oneList t i j++CoreTest.colored t.graph c)=true

instance (t : Setup d r n k) : Decidable (singleChecks t) :=
  inferInstanceAs (Decidable (∀ i j c,EdgeWalk.passes t.root (oneList t i j++CoreTest.colored t.graph c)=true))

theorem singles_work (t : Setup d r n k) (test : singleChecks t) (i j : Fin d) :
    passes (Joined t.graph t.fixed.toFinset) t.point t.dest (oneCell i j) := by
  intro c x y
  have path := CoreTest.to_graph t.graph (oneList t i j) c
    (EdgeWalk.connected_of_passes _ _ (test i j c) x y)
  have step {a b} (h : (a,b)∈oneList t i j) :
      extend (Joined t.graph t.fixed.toFinset c) t.point t.dest (oneCell i j) a b := by
    rcases List.mem_append.mp h with old|fresh
    · exact Or.inl (Or.inl (Or.inl (List.mem_toFinset.mpr old)))
    · obtain ⟨l,_,m,ok,eq⟩ := (by simpa only [List.mem_flatMap,List.mem_map] using fresh :
        ∃ l∈List.finRange d,∃ m∈(List.finRange d).filter (fun b => decide (l=i ↔ b=j)),(t.point l,t.dest m)=(a,b))
      cases eq
      exact Or.inr ⟨l,m,(of_decide_eq_true (List.mem_filter.mp ok).2 : l=i ↔ m=j),Or.inl ⟨rfl,rfl⟩⟩
  apply path.mapInto id
  intro a b h
  apply Walk.step (.stay _)
  rcases h with (e|e)|color
  · exact step (List.mem_toFinset.mp e)
  · exact extend_symm (fun w => joined_symm t.graph w) (step (List.mem_toFinset.mp e))
  · exact Or.inl (Or.inr color)

/-- If all singleton tests pass on a blocked five-slot choice, each
permutation is blocked at the level of a pair of slots. -/
theorem pair_blocks (t : Setup 5 r n k) {b} (h : Sharp t b) (s : singleChecks t) (p : Perm (Fin 5)) :
    ∃ A : Finset (Fin 5),A.card=2 ∧
      ¬passes (Joined t.graph t.fixed.toFinset) t.point t.dest (splitLinks A (A.map p.toEmbedding)) := by
  classical
  by_contra! no
  have yes := (five_sides (Joined t.graph t.fixed.toFinset) (fun _ {_ _} e => joined_symm t.graph e)
    t.point t.dest p).mpr ⟨fun i => singles_work t s i (p i),no⟩
  exact h.2.2.1 ⟨p,fun c _ => (works_draw _ _ _ _ _).mpr yes c⟩

/-- The target colors form the unique smallest obstruction, characterizing every palette. -/
theorem palette_iff (t : Setup d r n k) {b : Nat} (sharp : Sharp t b) (S : Finset (Fin k)) :
    palette t S ↔ ¬target t⊆S := by
  classical
  refine ⟨fun ⟨p,win⟩ sub => sharp.2.2.1 ⟨p,fun c hc => win c (sub hc)⟩,?_⟩
  intro missing
  obtain ⟨c,hc,out⟩ := Finset.not_subset.mp missing
  obtain ⟨h,_,rfl⟩ := mem_map.mp hc
  obtain ⟨p,ok,_,_⟩ := sharp.2.2.2 h
  exact ⟨p,fun c hc => ok c (fun eq => out (eq ▸ hc))⟩

/-- Read a square table of edge colors, one vertex per row. -/
def parseRows (s : String) : Array (Array Nat) :=
  ((s.trim.splitOn "\n").map fun line => (((line.splitOn " ").filter (·!="")).map String.toNat!).toArray).toArray

def fromRows {n : Nat} [NeZero n] (rows : Array (Array Nat)) (x y : Fin (n+1)) : Fin n :=
  Fin.ofNat' n ((rows[x.val]!)[y.val]!)

def setup {m k : Nat} (d : Nat) [NeZero m] (g : Coloring m k) (hk : r≤k)
    (fixed : List (Nat × Nat)) (u v : Array Nat) : Setup d r m k where
  graph := g
  fixed := fixed.map fun e => (Fin.ofNat' m e.1,Fin.ofNat' m e.2)
  point i := Fin.ofNat' m u[i.val]!
  dest i := Fin.ofNat' m v[i.val]!
  root := 0
  key := Fin.castLEEmb hk

/-- In a minimum proper coloring of an even order, adding the last vertex
to an optimal drawing of the restricted coloring preserves the optimum. -/
theorem exact_complete {n : Nat} (g : Coloring (n+1) n) (hn : 3≤n+1)
    (odd : Exact (restrict g) ((2*n+2)/3)) : Exact g ((2*n+2)/3) := by
  obtain ⟨w,legal,size,win⟩ := odd.1
  exact exact_of_upper (upper_from_deletion g ⟨w,legal,size.le,win⟩) (fun _ => even_lower hn g)

end WildSlots.Certificates
