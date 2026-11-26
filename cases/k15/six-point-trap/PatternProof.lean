import PatternChecks
import BoundaryProof
namespace SixBoundary
open VertexRedraw

private theorem filled (f : Nat → Nat) (ks : List Nat) (a : Array Nat) (q : Nat)
    (bound : q<a.size) (written : q∈ks ∨ a[q]?=some (f q)) :
    (ks.foldl (fun acc k => acc.set! k (f k)) a)[q]?=some (f q) := by
  induction ks generalizing a with
  | nil => exact written.resolve_left (by simp)
  | cons k ks ih =>
    apply ih _ (by simpa using bound)
    by_cases eq : k=q
    · subst k
      exact Or.inr (by simp [Array.getElem?_setIfInBounds_self_of_lt,bound])
    · rcases written with mem|known
      · exact Or.inl ((List.mem_cons.mp mem).resolve_left (Ne.symm eq))
      · exact Or.inr (by simpa [eq] using known)

private theorem table_entry {t q : Nat} (ht : t∈starters) (mem : q∈t::outside t) :
    (table t)[q]! = allowed t q := by
  have limits : (starters.all (· < 65536))=true ∧ (fours.all (· < 65536))=true := by native_decide
  have lt : q<65536 := by
    rcases List.mem_cons.mp mem with rfl|out
    · exact of_decide_eq_true (List.all_eq_true.mp limits.1 _ ht)
    · exact of_decide_eq_true (List.all_eq_true.mp limits.2 _ (List.mem_filter.mp out).1)
  have present : q∈outside t ++ [t] := by simpa [List.mem_append,or_comm] using mem
  have entry := filled (allowed t) (outside t++[t]) (Array.replicate 65536 0) q
    (by simpa using lt) (Or.inl present)
  have value : (table t)[q]?=some (allowed t q) := by simpa [List.foldl_append,table] using entry
  simp [getElem!_def,value]

private theorem partner_agrees (f : C→V→V) (inv : ∀ c x,f c (f c x)=x)
    (agree : ∀ c x,x.val<6 → f c x=ref c x) (c : C) (x : V) (known : held c x=true) :
    f c x=ref c x := by
  simp only [held,Bool.or_eq_true,decide_eq_true_eq] at known
  rcases known with h|h
  · exact agree _ _ h
  · have ri : ∀ k v,ref k (ref k v)=v := by native_decide
    have eq := agree c (ref c x) h
    rw [ri] at eq
    exact (congrArg (f c) eq).symm.trans (inv c (ref c x))

/-- If three colors could pair the four starters internally, then every choice
of three outside boxes still has at least one color whose image fits no box. -/
theorem no_pattern_completion (f : C→V→V) (inv : ∀ c x,f c (f c x)=x)
    (agree : ∀ c x,x.val<6 → f c x=ref c x)
    (t a b d : Nat) (ht : t∈starters) (ha : a∈outside t) (hb : b∈outside t) (hd : d∈outside t)
    (ab : a<b) (bd : b<d) (dis : a &&& b=0) (complement : 65535 ^^^ t ^^^ a ^^^ b=d)
    (interior : 3 ≤ internalCount t) :
    ¬ (∀ c : C, ∃ q∈[t,a,b,d],∀ x : V,t.testBit x.val = q.testBit (f c x).val) := by
  intro expected
  have allowedBox (c : C) : ∃ q∈[t,a,b,d],canMap t q c=true := by
    obtain ⟨q,hq,eq⟩ := expected c
    refine ⟨q,hq,List.all_eq_true.mpr ?_⟩
    intro x _
    cases hx : held c x with
    | false => simp [hx]
    | true => simp [hx,←partner_agrees f inv agree c x hx,eq x]
  have lookupTable (q) (mem : q∈t::outside t) : (table t)[q]! = allowed t q :=
    table_entry ht mem
  have keys := lookupTable t (List.mem_cons_self ..)
  have yes : (table t)[t]! ||| (table t)[a]! ||| (table t)[b]! ||| (table t)[d]! =32767 := by
    rw [keys,lookupTable a (List.mem_cons_of_mem _ ha),lookupTable b (List.mem_cons_of_mem _ hb),
      lookupTable d (List.mem_cons_of_mem _ hd)]
    apply Nat.eq_of_testBit_eq
    intro i
    have rhs : (32767 : Nat).testBit i=decide (i<15) := Nat.testBit_two_pow_sub_one 15 i
    simp only [Nat.testBit_or,allowed,bit_lookup,rhs]
    by_cases small : i<15
    · let c : C := ⟨i,small⟩
      have index : colors[i]?=some c := (by decide : ∀ c : C,colors[c.val]?=some c) c
      obtain ⟨q,hq,can⟩ := allowedBox c
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hq
      rcases hq with rfl|rfl|rfl|rfl <;> simp [index,small,can]
    · have len : colors.length≤i := by simpa [colors] using Nat.le_of_not_gt small
      simp [List.getElem?_eq_none len,small]
  have matchFound : possibleBox t=true := by
    apply Bool.and_eq_true_iff.mpr
    exact ⟨decide_eq_true interior,List.any_eq_true.mpr ⟨a,ha,List.any_eq_true.mpr
      ⟨b,hb,by simp [complement,ab,bd,dis,yes]⟩⟩⟩
  have mem := List.mem_filter.mpr (And.intro ht matchFound)
  have empty : starters.filter possibleBox=[] := List.isEmpty_iff.mp no_boxes.2
  rw [empty] at mem
  contradiction
#print axioms no_pattern_completion
end SixBoundary
