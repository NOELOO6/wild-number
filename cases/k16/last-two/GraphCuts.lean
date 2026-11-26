import Bounds
namespace SixBlockCuts
open Finset WildCuts EdgeWalk WildDeletion
abbrev V := Fin 16
abbrev G := Fin 6
abbrev P := Equiv.Perm V

def label (p : P) (v : V) := groups16.tag (p.symm v)
def sealed (p : P) (m : List (Edge 16)) (s : Finset G) :=
  ∀ x y, Adj m x y → (label p x ∈ s ↔ label p y ∈ s)

private theorem parity (p q : P) (m : List (Edge 16))
    (colored : ∀ x, x ≠ (pairs 16).rep ((pairs 16).tag x) →
      Adj m (q x) (q ((pairs 16).rep ((pairs 16).tag x))))
    (s : Finset G) (hs : sealed p m s) : s.card%2=0 := by
  let a := (side groups16 s).map p.toEmbedding
  let j := (univ : Finset (Fin 8)).filter (fun g => label p (q ((pairs 16).rep g)) ∈ s)
  have equiv (x : V) : label p (q x) ∈ s ↔ label p (q ((pairs 16).rep ((pairs 16).tag x))) ∈ s := by
    by_cases h : x = (pairs 16).rep ((pairs 16).tag x)
    · exact Iff.of_eq (congrArg (fun z => label p (q z) ∈ s) h)
    · exact hs _ _ (colored x h)
  have eq : a = (side (pairs 16) j).map q.toEmbedding := by
    ext v
    simpa [a,j,side,Finset.mem_map_equiv,label] using equiv (q.symm v)
  have cards := congrArg Finset.card eq
  simp only [a,Finset.card_map] at cards
  have oddBlocks : ∀ t : Finset G, (side groups16 t).card%2 = t.card%2 := by native_decide
  have pairsEven : ∀ t : Finset (Fin 8), (side (pairs 16) t).card%2 = 0 := by native_decide
  rw [← oddBlocks, cards, pairsEven]

private theorem together (p : P) (x : V) (m : List (Edge 16)) :
    Walk (Adj (wild groups16 p ++ m)) x (p (groups16.rep (label p x))) := by
  let v := p.symm x
  by_cases h : v = groups16.rep (groups16.tag v)
  · have eq := congrArg p h
    have eq' : x = p (groups16.rep (label p x)) := by simpa [v,label] using eq
    rw [← eq']; exact .stay _
  · have e := wild_step groups16 p v h
    apply Walk.step (.stay _)
    simpa [v,label,Adj,List.mem_append] using e.imp (Or.inl (b:=_)) (Or.inl (b:=_))

private theorem pair_witness (s : Finset G) (h : s.card=2) : ∃ i j : G, i∈s ∧ j∉s := by
  have all : ∀ u : Finset G, u.card=2 → ∃ i j : G, i∈u ∧ j∉u := by decide
  exact all s h

/-- For any placement of five triples and a singleton and any perfect
matching, graph failure is exactly closure of one of the fifteen block pairs. -/
theorem fails_iff (p q : P) (m : List (Edge 16))
    (colored : ∀ x, x ≠ (pairs 16).rep ((pairs 16).tag x) →
      Adj m (q x) (q ((pairs 16).rep ((pairs 16).tag x)))) :
    ¬ Connected (Adj (wild groups16 p ++ m)) ↔ ∃ s : Finset G, s.card=2 ∧ sealed p m s := by
  classical
  let E := Adj (wild groups16 p ++ m)
  constructor
  · intro fail
    change ¬ ∀ x y, Walk E x y at fail
    push_neg at fail
    obtain ⟨x,y,miss⟩ := fail
    let s := univ.filter (fun i => Walk E x (p (groups16.rep i)))
    have hub (v : V) : label p v ∈ s ↔ Walk E x v := by
      simp only [s,Finset.mem_filter,Finset.mem_univ,true_and]
      have trip := together p v m
      constructor
      · intro u
        have back {i j : V} (h : Walk E i j) : Walk E j i := by
          induction h with
          | stay => exact .stay _
          | step _ e ih => exact (Walk.step (E:=E) (.stay _) e.symm).join ih
        exact u.join (back trip)
      · exact fun h => h.join trip
    have closed : sealed p m s := by
      intro a b ab
      rw [hub,hub]
      have e : E a b := ab.imp (List.mem_append_right _) (List.mem_append_right _)
      exact ⟨fun h => .step h e,fun h => .step h e.symm⟩
    have hx := (hub x).mpr (Walk.stay x)
    have hy : label p y ∉ s := fun h => miss ((hub y).mp h)
    have even := parity p q m colored s closed
    have possibilities : ∀ t : Finset G, ∀ i j : G, i∈t → j∉t → t.card%2=0 →
        t.card=2 ∨ tᶜ.card=2 := by decide
    rcases possibilities s _ _ hx hy even with a | b
    · exact ⟨s,a,closed⟩
    · exact ⟨sᶜ,b,fun i j e => by simpa using not_congr (closed i j e)⟩
  · rintro ⟨s,two,closed⟩ conn
    obtain ⟨i,j,yes,no⟩ := pair_witness s two
    have wildSame (a b : V) (ab : (a,b) ∈ wild groups16 p) : label p a = label p b := by
      obtain ⟨v,_,eq⟩ := List.mem_map.mp ab
      have left := congrArg Prod.fst eq
      have right := congrArg Prod.snd eq
      simp only at left right
      rw [←left,←right]
      simp [label,groups16.section_]
    have inv {a b : V} (e : E a b) : label p a ∈ s ↔ label p b ∈ s := by
      rcases e with h | h
      · rcases List.mem_append.mp h with h | h
        · rw [wildSame _ _ h]
        · exact closed _ _ (Or.inl h)
      · rcases List.mem_append.mp h with h | h
        · rw [wildSame _ _ h]
        · exact closed _ _ (Or.inr h)
    have along {a b : V} (w : Walk E a b) : label p a ∈ s ↔ label p b ∈ s := by
      induction w with
      | stay => rfl
      | step _ e ih => exact ih.trans (inv e)
    have eq := along (conn (p (groups16.rep i)) (p (groups16.rep j)))
    simp [label,groups16.section_,yes,no] at eq
noncomputable def closedPairs (p : P) (m : List (Edge 16)) : Finset (Finset G) := by
  classical
  exact univ.filter (fun s => s.card = 2 ∧ sealed p m s)

/-- Multiple closed two-block cuts in one drawing are exactly the three
disjoint pairs partitioning the six blocks. This justifies subtracting two
extra cut counts whenever the three-pair partition is recorded. -/
theorem zero_one_or_three (p q : P) (m : List (Edge 16))
    (colored : ∀ x, x ≠ (pairs 16).rep ((pairs 16).tag x) →
      Adj m (q x) (q ((pairs 16).rep ((pairs 16).tag x)))) :
    (closedPairs p m).card ≤ 1 ∨ ∃ a b : Finset G,
      a.card=2 ∧ b.card=2 ∧ Disjoint a b ∧
      closedPairs p m = {a,b,(a∪b)ᶜ} ∧ (closedPairs p m).card=3 := by
  classical
  let f := closedPairs p m
  have mem (v : Finset G) : v∈f ↔ v.card=2 ∧ sealed p m v := by simp [f,closedPairs]
  by_cases small : f.card ≤ 1
  · exact Or.inl small
  right
  obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge small)
  obtain ⟨h0,h1⟩ := (mem a).mp ha
  obtain ⟨k0,k1⟩ := (mem b).mp hb
  have both {s t : Finset G} (hs : sealed p m s) (ht : sealed p m t) :
      (s ∩ t).card % 2 = 0 := parity p q m colored _ (fun x y e => by
        simp only [Finset.mem_inter]; exact and_congr (hs x y e) (ht x y e))
  have config : ∀ v w : Finset G, v.card=2 → w.card=2 → v≠w → (v ∩ w).card%2=0 →
      Disjoint v w ∧ (v∪w)ᶜ.card=2 ∧ ({v,w,(v∪w)ᶜ} : Finset (Finset G)).card=3 ∧
      ∀ u : Finset G, u.card=2 → (u∩v).card%2=0 → (u∩w).card%2=0 →
      u ∈ ({v,w,(v∪w)ᶜ} : Finset (Finset G)) := by native_decide
  obtain ⟨dis,rem,three,possible⟩ := config a b h0 k0 ne (both h1 k1)
  have remaining : (a∪b)ᶜ ∈ f := (mem _).mpr ⟨rem,fun x y e => by
    simp only [Finset.mem_compl,Finset.mem_union]
    exact not_congr (or_congr (h1 x y e) (k1 x y e))⟩
  have eq : f = {a,b,(a∪b)ᶜ} := by
    ext u
    constructor
    · intro hu
      obtain ⟨n,cl⟩ := (mem u).mp hu
      exact possible u n (both cl h1) (both cl k1)
    · simp only [Finset.mem_insert,Finset.mem_singleton]
      rintro (rfl|rfl|rfl) <;> assumption
  exact ⟨a,b,h0,k0,dis,eq,(congrArg Finset.card eq).trans three⟩
#print axioms zero_one_or_three
#print axioms fails_iff
end SixBlockCuts
