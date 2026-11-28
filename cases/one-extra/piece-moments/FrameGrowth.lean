import FrozenStats
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

namespace WildSieve.FrameGrowth
open Finset
variable {A C : Type} [LinearOrder A] [Fintype A] [Fintype C]

def collisions (F : Factor A C) (B : Finset A) := ∑ c,(Inside F c B).choose 2

omit [Fintype A] [Fintype C] in
private theorem insert_bound (F : Factor A C) (B : Finset A) (c : C) (x : A) :
    Inside F c (insert x B)≤Inside F c B+(if F.f c x∈B then 1 else 0) := by
  classical
  let f := F.f c
  by_cases partner : f x∈B
  · have sub : lowerEnds f (insert x B)⊆insert (min x (f x)) (lowerEnds f B) := by
      intro z hz
      obtain ⟨zx,lt,fz⟩ := mem_filter.mp hz
      rcases mem_insert.mp zx with rfl|zb
      · exact mem_insert.mpr (Or.inl (min_eq_left lt.le).symm)
      · rcases mem_insert.mp fz with eq|fb
        · have e : f x=z := eq ▸ F.invol c z
          exact mem_insert.mpr (Or.inl (by rw [e]; exact (min_eq_right (eq ▸ lt.le)).symm))
        · exact mem_insert_of_mem (mem_filter.mpr ⟨zb,lt,fb⟩)
    simpa [Inside,f,partner] using (card_le_card sub).trans (card_insert_le _ _)
  · have sub : lowerEnds f (insert x B)⊆lowerEnds f B := by
      intro z hz
      obtain ⟨zx,lt,fz⟩ := mem_filter.mp hz
      rcases mem_insert.mp zx with rfl|zb
      · exact (partner ((mem_insert.mp fz).resolve_left lt.ne.symm)).elim
      · rcases mem_insert.mp fz with eq|fb
        · have inv : f (f z)=z := F.invol c z
          rw [eq] at inv
          exact (partner (inv.symm ▸ zb)).elim
        · exact mem_filter.mpr ⟨zb,lt,fb⟩
    simpa [Inside,f,partner] using card_le_card sub

/-- The additional pairs charged at x, summed by the color of the new edge. -/
def charge (F : Factor A C) (B : Finset A) (x : A) :=
  ∑ c,if F.f c x∈B then Inside F c B else 0

omit [Fintype A] in
theorem insert_cost (F : Factor A C) (B : Finset A) (x : A) :
    collisions F (insert x B)≤collisions F B+charge F B x := by
  unfold collisions charge
  rw [←sum_add_distrib]
  apply sum_le_sum
  intro c _
  have le := Nat.choose_le_choose 2 (insert_bound F B c x)
  by_cases h : F.f c x∈B
  · simp only [h,if_true,Nat.choose_succ_succ,Nat.choose_one_right] at le ⊢
    simpa [Nat.add_comm] using le
  · simpa [h] using le

private theorem growth_identity (b k : Nat) (fits : 2*k≤b) :
    (b-2*k)*k+4*k.choose 2=k*(b-2) := by
  by_cases zero : k=0
  · simp [zero]
  · have k1 : 1≤k := by omega
    have b2 : 2≤b := by omega
    have bin := Nat.choose_succ_right_eq k 1
    simp only [Nat.choose_one_right] at bin
    have a : b=(b-2*k)+2*k := by omega
    have c : b=(b-2)+2 := by omega
    have d : k=(k-1)+1 := by omega
    nlinarith only [bin,congrArg (fun z => z*k) a,congrArg (fun z => z*k) c,congrArg (fun z => z*k) d]

/-- An already repeated pair removes four charges from the bound on the next step. -/
theorem charge_balance (F : Factor A C) (B : Finset A) :
    (∑ x∈Bᶜ,charge F B x)+4*collisions F B=B.card.choose 2*(B.card-2) := by
  classical
  unfold charge collisions
  rw [sum_comm,←sum_inside F B,sum_mul,mul_sum,←sum_add_distrib]
  apply sum_congr rfl
  intro c _
  have same : Bᶜ.filter (fun x => F.f c x∈B)=forced (F.f c) B B := by
    ext x
    simp only [mem_filter,mem_compl,forced,mem_sdiff,mem_image]
    constructor
    · rintro ⟨nx,fx⟩
      exact ⟨⟨_,fx,F.invol c x⟩,nx⟩
    · rintro ⟨⟨y,hy,rfl⟩,nx⟩
      exact ⟨nx,by rwa [F.invol c y]⟩
  rw [←sum_filter,sum_const,nsmul_eq_mul,same,external_size (F.invol c) (F.moving c)]
  exact growth_identity _ _ (ends_bound (F.invol c) B)

theorem sum_charge (F : Factor A C) (B : Finset A) :
    (∑ x∈Bᶜ,charge F B x)≤B.card.choose 2*(B.card-2) := by
  have := charge_balance F B
  omega

/-- Counts extensions that add at most e repeated pairs. The four-charge saving
from each existing collision also applies when the current frame is not rainbow. -/
theorem extension_choices (F : Factor A C) (B : Finset A) (e : Nat) :
    Fintype.card A-B.card-
      ((B.card.choose 2*(B.card-2)-4*collisions F B)/(e+1)) ≤
      (Bᶜ.filter (fun x => collisions F (insert x B)≤collisions F B+e)).card := by
  classical
  let bad := Bᶜ.filter (fun x => e<charge F B x)
  have bound := sum_le_sum (s:=bad) (fun x hx =>
    show e+1≤charge F B x from (mem_filter.mp hx).2)
  rw [sum_const,nsmul_eq_mul] at bound
  have total := sum_le_sum_of_subset_of_nonneg (s:=bad) (t:=Bᶜ)
    (filter_subset _ _) (fun x _ _ => Nat.zero_le (charge F B x))
  have balance := charge_balance F B
  have cap : bad.card≤(B.card.choose 2*(B.card-2)-4*collisions F B)/(e+1) := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    exact bound.trans (total.trans (by omega))
  have sub : Bᶜ \ bad ⊆ Bᶜ.filter (fun x => collisions F (insert x B)≤collisions F B+e) := by
    intro x hx
    obtain ⟨out,good⟩ := mem_sdiff.mp hx
    have cost : charge F B x≤e := le_of_not_gt (fun high => good (mem_filter.mpr ⟨out,high⟩))
    exact mem_filter.mpr ⟨out,(insert_cost F B x).trans (Nat.add_le_add_left cost _)⟩
  have size := card_sdiff (show bad⊆Bᶜ from filter_subset _ _)
  rw [card_compl] at size
  have := card_le_card sub
  omega

/-- At least one exterior vertex costs at most the floor of the mean. -/
theorem extend (F : Factor A C) (B : Finset A) (room : B.card<Fintype.card A) :
    ∃ x∉B,collisions F (insert x B)≤collisions F B+B.card.choose 2*(B.card-2)/(Fintype.card A-B.card) := by
  classical
  let q := B.card.choose 2*(B.card-2)
  let outside := Fintype.card A-B.card
  have pos : 0<outside := by dsimp [outside]; omega
  have den : Bᶜ.card=outside := card_compl _
  have enough := sum_charge F B
  have existsSmall : ∃ x∈Bᶜ,charge F B x≤q/outside := by
    by_contra! bad
    have lo := sum_le_sum (s:=Bᶜ) (fun x hx => show q/outside+1≤charge F B x by exact bad x hx)
    rw [sum_const,nsmul_eq_mul,den] at lo
    have up : q<outside*(q/outside+1) := by
      rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul pos).mp (Nat.lt_succ_self _)
    change outside*(q/outside+1)≤∑ x∈Bᶜ,charge F B x at lo
    exact (Nat.not_le_of_gt up) (lo.trans enough)
  obtain ⟨x,hx,h⟩ := existsSmall
  exact ⟨x,mem_compl.mp hx,(insert_cost F B x).trans (Nat.add_le_add_left h _)⟩

/-- Build a frame through any specified root. -/
theorem at_root (F : Factor A C) (r : A) (k : Nat) (room : k<Fintype.card A) :
    ∃ B : Finset A,r∈B ∧ B.card=k+1 ∧ collisions F B ≤
      ∑ b∈range (k+1),b.choose 2*(b-2)/(Fintype.card A-b) := by
  classical
  induction k with
  | zero =>
    refine ⟨{r},by simp,by simp,?_⟩
    have one (c : C) : Inside F c {r}≤1 := (card_le_card (filter_subset _ _)).trans (card_singleton _).le
    have zero (c : C) : (Inside F c {r}).choose 2=0 := Nat.choose_eq_zero_of_lt (by have := one c; omega)
    simp [collisions,zero]
  | succ k ih =>
    obtain ⟨B,hr,sz,budget⟩ := ih (by omega)
    obtain ⟨x,hx,h⟩ := extend F B (by omega)
    refine ⟨insert x B,mem_insert_of_mem hr,by simp [hx,sz],?_⟩
    rw [sum_range_succ]
    rw [sz] at h
    exact h.trans (Nat.add_le_add_right budget _)

#print axioms at_root
end WildSieve.FrameGrowth
