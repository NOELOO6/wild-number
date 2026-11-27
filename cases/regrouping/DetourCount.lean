import PartnerSwitch
import MatchingCuts
namespace WildExact.Regroup.Switch
open Finset WildDeletion
variable {V I J : Type} [Fintype I] [DecidableEq J]

private def layer (W : V → V → Prop) (l r : J → V) (R : Finset J) (a b : V) :=
  W a b ∨ ∃ e∈R,(a=l e ∧ b=r e) ∨ (a=r e ∧ b=l e)

omit [DecidableEq J] in
private theorem locally_connected (W : V → V → Prop) (l r : J → V) (R : Finset J)
    {a b : V} (h : Walk W a b) : Walk (layer W l r R) a b :=
  Walk.mapInto (E:=W) id (fun _ _ e => .step (.stay _) (Or.inl e)) h

omit [DecidableEq J] in
private theorem grow (W : V → V → Prop) (l r : J → V) {R T : Finset J} (sub : R⊆T)
    {a b : V} (h : Walk (layer W l r R) a b) : Walk (layer W l r T) a b := by
  apply h.mapInto id
  rintro u v (e|⟨k,hk,eq⟩)
  · exact .step (.stay _) (Or.inl e)
  · exact .step (.stay _) (Or.inr ⟨k,sub hk,eq⟩)

omit [DecidableEq J] in
private theorem layer_sym (W : V → V → Prop) (sym : ∀ {a b},W a b → W b a) (l r : J → V)
    (R : Finset J) : ∀ {a b},layer W l r R a b → layer W l r R b a := by
  rintro a b (e|⟨i,hi,ab|ba⟩)
  · exact Or.inl (sym e)
  · exact Or.inr ⟨i,hi,Or.inr ab.symm⟩
  · exact Or.inr ⟨i,hi,Or.inl ba.symm⟩

/-- A connected graph made from already joined groups needs at most one
fewer added edge than there are group names. The added edges are labeled,
so parallel edges and loops are allowed. -/
private theorem span [Nonempty V] (tag : V → I) (W : V → V → Prop)
    (sym : ∀ {a b},W a b → W b a) (group : ∀ a b,tag a=tag b → Walk W a b)
    (l r : J → V) (all : Finset J) (full : Connected (layer W l r all)) :
    ∃ R⊆all,R.card<Fintype.card I ∧ Connected (layer W l r R) := by
  classical
  let z : V := Classical.choice ‹Nonempty V›
  let seen (R : Finset J) := univ.filter (fun i => ∃ v,tag v=i ∧ Walk (layer W l r R) z v)
  have mem (R : Finset J) (v : V) : tag v∈seen R ↔ Walk (layer W l r R) z v := by
    constructor
    · intro h
      obtain ⟨u,eq,route⟩ := (mem_filter.mp h).2
      exact route.join (locally_connected W l r R (group u v eq))
    · intro h
      exact mem_filter.mpr ⟨mem_univ _,v,rfl,h⟩
  have finish (k : Nat) (R : Finset J) (sub : R⊆all) (paid : R.card<(seen R).card)
      (slack : Fintype.card I-(seen R).card≤k) :
      ∃ T⊆all,T.card<Fintype.card I ∧ Connected (layer W l r T) := by
    induction k using Nat.strong_induction_on generalizing R with
    | h k ih =>
      by_cases done : ∀ v,Walk (layer W l r R) z v
      · exact ⟨R,sub,paid.trans_le (seen R).card_le_univ,fun a b => (backwards (layer_sym W sym l r R) (done a)).join (done b)⟩
      · have cross : ∃ a b, Walk (layer W l r R) z a ∧ layer W l r all a b ∧ ¬Walk (layer W l r R) z b := by
          by_contra! none
          apply done
          intro v
          have reach {a b} (p : Walk (layer W l r all) a b) (ha : Walk (layer W l r R) z a) : Walk (layer W l r R) z b := by
            induction p with
            | stay => exact ha
            | step _ e ih => exact none _ _ ih e
          exact reach (full z v) (.stay _)
        obtain ⟨a,b,ha,edge,out⟩ := cross
        rcases edge with w|⟨e,ea,ends⟩
        · exact (out (.step ha (Or.inl w))).elim
        have old : R⊆insert e R := subset_insert _ _
        have more : Walk (layer W l r (insert e R)) z b := .step (grow W l r old ha) (Or.inr ⟨e,mem_insert_self _ _,ends⟩)
        have incl : seen R ⊆ seen (insert e R) := by
          intro i hi
          obtain ⟨v,eq,path⟩ := (mem_filter.mp hi).2
          exact mem_filter.mpr ⟨mem_univ _,v,eq,grow W l r old path⟩
        have strict := card_lt_card (ssubset_of_subset_of_ne incl (fun eq => out ((mem R b).mp (eq ▸ (mem _ b).mpr more))))
        have max := (seen (insert e R)).card_le_univ
        have cost := card_insert_le e R
        apply ih (Fintype.card I-(seen (insert e R)).card) (by omega) (insert e R) (insert_subset ea sub) (by omega) le_rfl
  exact finish _ ∅ (empty_subset _) (by simpa only [card_empty] using card_pos.mpr ⟨tag z,(mem ∅ z).mpr (.stay _)⟩) le_rfl

/-- In one connected piece, at least |V|/2 minus the number of wild
groups plus one matching edges have detours. Count each edge by its smaller
endpoint. The chosen detour uses none of the matching edge in question. -/
theorem many_detours [Fintype V] [LinearOrder V] [Nonempty V] (tag : V → I)
    (W : V → V → Prop) (sym : ∀ {a b},W a b → W b a)
    (group : ∀ a b,tag a=tag b → Walk W a b)
    (m : V → V) (inv : Function.Involutive m) (free : ∀ v,v≠m v)
    (connected : Connected (WithMatching W m)) :
    ∃ U : Finset V, Fintype.card V+2≤2*U.card+2*Fintype.card I ∧
      ∀ x∈U,x<m x ∧ Walk (fun a b => W a b ∨ (a≠x ∧ a≠m x ∧ m a=b)) x (m x) := by
  classical
  let M := WildSieve.lowerEnds m univ
  have ends (x) : x∈M ↔ x<m x := by simp [M,WildSieve.lowerEnds]
  have count := WildSieve.closed_size inv free (show WildSieve.Closed m univ from fun _ _ => mem_univ _)
  change (univ : Finset V).card=2*M.card at count
  rw [card_univ] at count
  have conn : Connected (layer W id m M) := by
    intro a b
    apply (connected a b).mapInto id
    rintro u v (eq|w|matched)
    · exact eq ▸ .stay _
    · exact .step (.stay _) (Or.inl w)
    · subst v
      rcases lt_or_gt_of_ne (free u) with lt|gt
      · exact .step (.stay _) (Or.inr ⟨u,(ends _).mpr lt,Or.inl ⟨rfl,rfl⟩⟩)
      · exact .step (.stay _) (Or.inr ⟨m u,(ends _).mpr (by rwa [inv u]),Or.inr ⟨(inv u).symm,rfl⟩⟩)
  obtain ⟨R,sub,budget,spanR⟩ := span tag W sym group id m M conn
  have num := card_sdiff_add_card_eq_card sub
  refine ⟨M \ R,by omega,?_⟩
  intro x hx
  obtain ⟨mx,xr⟩ := mem_sdiff.mp hx
  refine ⟨(ends x).mp mx,?_⟩
  apply (spanR x (m x)).mapInto id
  rintro a b (w|⟨k,hk,h⟩)
  · exact .step (.stay _) (Or.inl w)
  · have kx : k≠x := fun eq => xr (eq ▸ hk)
    have kp := (ends k).mp (sub hk)
    have xp := (ends x).mp mx
    have kn : k≠m x := fun eq => xp.asymm (by simpa only [eq,inv x] using kp)
    rcases h with ⟨u,v⟩|⟨u,v⟩
    · rw [u,v]
      exact .step (.stay _) (Or.inr ⟨kx,kn,rfl⟩)
    · rw [u,v]
      exact .step (.stay _) (Or.inr ⟨fun eq => kn ((inv k).symm.trans (congrArg m eq)),
        fun eq => kx (inv.injective eq),inv k⟩)

#print axioms many_detours
end WildExact.Regroup.Switch
