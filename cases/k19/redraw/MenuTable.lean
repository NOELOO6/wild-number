import MenuProof
namespace WildMenu
open WildCuts Finset

def mask (s : Finset V) := (key s).2
def vertex (n : Nat) : V := ⟨n%19,by omega⟩
def invert (f : V → V) (v : V) := ((List.finRange 19).find? (fun x => f x == v)).getD 0
def permutation (f : V → V) : Equiv.Perm V :=
  if h : ∀ x, invert f (f x) = x ∧ f (invert f x) = x then
    ⟨f,invert f,fun x => (h x).1,fun x => (h x).2⟩ else Equiv.refl _

def affine (a : Fin 18) (b : V) := permutation (fun x => vertex ((a.val+1)*x.val+b.val))
def affineMaps := (List.finRange 18).flatMap (fun a => (List.finRange 19).map (affine a))
structure Plan where
  weight : Nat
  place : Equiv.Perm V

def basePlan (line : String) : Plan :=
  let fields := line.splitOn " "
  let w := fields.head!.toNat!
  let labels := fields[1]!.toList.toArray.map (fun c => c.toNat-'0'.toNat)
  let points := ((List.finRange 19).mergeSort (fun x y => labels[x.val]! ≤ labels[y.val]!)).toArray
  ⟨w,permutation (fun v => points[v.val]!)⟩
def seeds := (((include_str "layout-weights.txt").trim.splitOn "\n").map basePlan)
def menu := seeds.flatMap (fun s => affineMaps.map (fun a => Plan.mk s.weight (s.place.trans a)))

def smallCuts := (List.finRange 31).map cut
def keys (r : Plan) := smallCuts.map (fun s => mask (s.map r.place.toEmbedding))
abbrev Hist := Std.HashMap Nat Nat
def value (h : Hist) (k : Nat) := h[k]?.getD 0
def add (h : Hist) (k w : Nat) := h.insert k (value h k + w)
def bumps (h : Hist) (ks : List Nat) (w : Nat) := ks.foldl (fun t j => add t j w) h
def tally (rs : List Plan) (base : Hist := ∅) :=
  rs.foldl (fun h r => bumps h (keys r) r.weight) base
def hist := tally menu
def weight := (menu.map Plan.weight).sum

private theorem bump_count (ks : List Nat) (k w : Nat) (h : Hist) :
    value (bumps h ks w) k = value h k + w*ks.count k := by
  induction ks generalizing h with
  | nil => simp [bumps]
  | cons a xs ih =>
    change value (bumps (add h a w) xs w) k = _
    rw [ih]
    by_cases eq : a=k
    · subst a; simp [add,value,List.count_cons_self,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    · simp [add,value,Std.HashMap.getElem?_insert,List.count_cons,eq,Ne.symm eq]

theorem tally_count (rs : List Plan) (k : Nat) (h : Hist) :
    value (tally rs h) k = value h k + (rs.map (fun r => r.weight*(keys r).count k)).sum := by
  induction rs generalizing h with
  | nil => simp [tally]
  | cons r rs ih =>
    simp only [tally,List.foldl_cons]
    have step := ih (bumps h (keys r) r.weight)
    unfold tally at step
    rw [step,bump_count]
    simp [Nat.add_assoc]
theorem hist_count (k : Nat) :
    value hist k = (menu.map (fun r => r.weight*(keys r).count k)).sum := by
  simpa [hist,value] using tally_count menu k ∅

def sideCodes (q : Equiv.Perm V) := fun j : Finset (Fin 10) => mask (closedSides q j)
def charge (q : Equiv.Perm V) := ∑ j, value hist (sideCodes q j)

private theorem swap_sum {I : Type} [Fintype I] (rs : List Plan) (f : I → Plan → Nat) :
    (rs.map (fun r => ∑ i, f i r)).sum = ∑ i, (rs.map (f i)).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih => simp [ih,Finset.sum_add_distrib]

/-- One draw from the same menu works for every color whenever the combined
weights of their possibly closed cuts are less than the weight of the menu. -/
theorem find_clean {C : Type} [Fintype C] (q : C → Equiv.Perm V) (budget : (∑ c, charge (q c)) < weight) :
    ∃ r ∈ menu, ∀ c i j, mask ((cut i).map r.place.toEmbedding) ≠ sideCodes (q c) j := by
  classical
  let cost (r : Plan) (c : C) (j : Finset (Fin 10)) := r.weight*(keys r).count (sideCodes (q c) j)
  have bound : (menu.map (fun r => ∑ c, ∑ j, cost r c j)).sum < (menu.map Plan.weight).sum := by
    rw [swap_sum]
    simp_rw [swap_sum]
    simpa only [charge,weight,hist_count,cost] using budget
  by_contra! no
  have bad (r : Plan) (hr : r ∈ menu) : r.weight ≤ ∑ c, ∑ j, cost r c j := by
    obtain ⟨c,i,j,eq⟩ := no r hr
    have mem : sideCodes (q c) j ∈ keys r := by
      rw [← eq]
      exact List.mem_map_of_mem (List.mem_map_of_mem (List.mem_finRange i))
    have pos := List.count_pos_iff.mpr mem
    calc
      _ ≤ cost r c j := by
        change r.weight ≤ r.weight*_
        simpa using Nat.mul_le_mul_left r.weight (show 1 ≤ _ from pos)
      _ ≤ ∑ t, cost r c t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
      _ ≤ _ := Finset.single_le_sum (f := fun d : C => ∑ t, cost r d t) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  exact (Nat.not_le_of_gt bound) (List.sum_le_sum (fun r hr => bad r hr))
end WildMenu
