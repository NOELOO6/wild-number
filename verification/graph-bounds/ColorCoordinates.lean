import GraphLayouts
import Mathlib.Data.Fintype.Sum

namespace WildCuts
open Finset EdgeWalk

def pairs (n : Nat) : Blocks (Fin n) (Fin ((n+1)/2)) where
  tag x := ⟨x.val/2,by omega⟩
  rep i := ⟨2*i.val,by omega⟩
  section_ i := by apply Fin.ext; dsimp; omega

abbrev Line (n : Nat) := {e : Fin n × Fin n // e.1 < e.2}

def endpoint {n : Nat} (e : Line n) (side : Bool) : Fin n := if side then e.1.2 else e.1.1

private theorem endpoints_injective {n : Nat} (m : List (Edge n)) (edges : Finset (Line n))
    (drawn : ∀ e ∈ edges, Adj m e.1.1 e.1.2)
    (proper : ∀ x y z, Adj m x y → Adj m x z → y = z) :
    Function.Injective (fun a : (↥edges) × Bool => endpoint a.1.1 a.2) := by
  intro ⟨⟨e,he⟩,a⟩ ⟨⟨f,hf⟩,b⟩ eq
  have em := drawn e he
  have fm := drawn f hf
  have eo := e.2
  have fo := f.2
  cases a <;> cases b <;> simp only [endpoint, Bool.false_eq_true, if_false, if_true] at eq
  · have h := proper _ _ _ em (eq ▸ fm)
    have same : e = f := Subtype.ext (Prod.ext eq h)
    subst f; rfl
  · have h := proper _ _ _ em (eq ▸ fm.symm)
    omega
  · have h := proper _ _ _ em.symm (eq ▸ fm)
    omega
  · have h := proper _ _ _ em.symm (eq ▸ fm.symm)
    have same : e = f := Subtype.ext (Prod.ext h eq)
    subst f; rfl

/-- Every minimum proper coloring has coordinates for the pairs of every
color. They are derived from ordinary graph adjacency and the edge count. -/
theorem coordinates {n k : Nat} {C : Type} [Fintype C] [DecidableEq C]
    (size : n / 2 = k) (total : Fintype.card (Line n) = Fintype.card C * k)
    (m : C → List (Edge n))
    (complete : ∀ x y : Fin n, x ≠ y → ∃ c, Adj (m c) x y)
    (proper : ∀ c x y z, Adj (m c) x y → Adj (m c) x z → y = z) :
    ∀ c, ∃ q : Equiv.Perm (Fin n), ∀ x, x ≠ (pairs n).rep ((pairs n).tag x) →
      Adj (m c) (q x) (q ((pairs n).rep ((pairs n).tag x))) := by
  classical
  let paint (e : Line n) := Classical.choose (complete e.1.1 e.1.2 e.2.ne)
  have painted (e : Line n) : Adj (m (paint e)) e.1.1 e.1.2 := Classical.choose_spec (complete e.1.1 e.1.2 e.2.ne)
  let es (c : C) := univ.filter (fun e : Line n => paint e = c)
  have drawn (c : C) (e : Line n) (he : e ∈ es c) : Adj (m c) e.1.1 e.1.2 :=
    (Finset.mem_filter.mp he).2 ▸ painted e
  have inj (c : C) := endpoints_injective (m c) (es c) (drawn c) (proper c)
  have limit (c : C) : (es c).card ≤ k := by
    have h := Fintype.card_le_of_injective _ (inj c)
    simp only [Fintype.card_prod,Fintype.card_coe,Fintype.card_bool,Fintype.card_fin] at h
    omega
  have count : (∑ c, (es c).card) = Fintype.card C * k := by
    rw [← total, ← Finset.card_univ]
    exact (Finset.card_eq_sum_card_fiberwise (f := paint) (fun _ _ => Finset.mem_univ _)).symm
  have full (c : C) : (es c).card = k := by
    by_contra h
    have lt : (∑ j, (es j).card) < ∑ _j : C, k :=
      Finset.sum_lt_sum (fun j _ => limit j) ⟨c,Finset.mem_univ _,lt_of_le_of_ne (limit c) h⟩
    simp [count] at lt
  intro c
  let name : Fin k ≃ ↥(es c) := Fintype.equivOfCardEq (by simp [full])
  let active := univ.filter (fun x : Fin n => x.val < 2*k)
  let idx (x : Fin n) (h : x ∈ active) : Fin k :=
    ⟨x.val/2,by have := (Finset.mem_filter.mp h).2; omega⟩
  let f (x : Fin n) := if h : x ∈ active then endpoint (name (idx x h)).1 (decide (x.val % 2 = 1)) else x
  have finj : Set.InjOn f (active : Set (Fin n)) := by
    intro x hx y hy e
    change x ∈ active at hx
    change y ∈ active at hy
    simp only [f, dif_pos hx, dif_pos hy] at e
    have same := (inj c) (a₁ := (name (idx x hx),decide (x.val % 2 = 1)))
      (a₂ := (name (idx y hy),decide (y.val % 2 = 1))) e
    have div := congrArg Fin.val (name.injective (congrArg Prod.fst same))
    have mod := congrArg Prod.snd same
    change x.val/2 = y.val/2 at div
    change decide (x.val % 2 = 1) = decide (y.val % 2 = 1) at mod
    simp only [decide_eq_decide] at mod
    apply Fin.ext; omega
  obtain ⟨q,hq⟩ := Finset.exists_equiv_extend_of_card_eq (t := (univ : Finset (Fin n)))
    (by simp) (Finset.subset_univ (active.image f)) finj
  let univEquiv : ↥(univ : Finset (Fin n)) ≃ Fin n :=
    ⟨Subtype.val,fun x => ⟨x,Finset.mem_univ _⟩,fun _ => rfl,fun _ => rfl⟩
  let relabel := q.trans univEquiv
  refine ⟨relabel,?_⟩
  intro x hx
  let y := (pairs n).rep ((pairs n).tag x)
  have yv : y.val = 2*(x.val/2) := rfl
  have odd : x.val % 2 = 1 := by
    by_contra no
    apply hx
    apply Fin.ext
    change x.val = y.val
    omega
  have ax : x ∈ active := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by have := x.isLt; omega⟩
  have ay : y ∈ active := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by have := x.isLt; omega⟩
  have qx : relabel x = f x := hq x ax
  have qy : relabel y = f y := hq y ay
  change Adj (m c) (relabel x) (relabel y)
  rw [qx,qy]
  have same : idx y ay = idx x ax := by apply Fin.ext; change y.val/2 = x.val/2; omega
  have even : ¬ y.val % 2 = 1 := by omega
  simpa only [f,dif_pos ax,dif_pos ay,odd,decide_true,even,decide_false,same,endpoint,
    if_true,Bool.false_eq_true,if_false] using (drawn c _ (name (idx x ax)).2).symm
end WildCuts
