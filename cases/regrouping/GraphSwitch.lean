import PartnerSwitch
import MatchingModel
import LegalEdges
namespace WildExact.Regroup.Switch
open Finset WildDeletion WildCuts
variable {n : Nat}

def exchangeLine (x y : Fin n) (e : Fin n × Fin n) :=
  ordered (Equiv.swap x y e.1,Equiv.swap x y e.2)
def exchangeLines (x y : Fin n) (w : Lines n) := w.image (exchangeLine x y)

private theorem unordered {a b u v : Fin n} :
    ordered (u,v)=(a,b) ∨ ordered (u,v)=(b,a) ↔ (u=a ∧ v=b) ∨ (u=b ∧ v=a) := by
  by_cases h : u≤v
  · simp [ordered,h,Prod.ext_iff]
  · simp [ordered,h,Prod.ext_iff]; tauto

theorem same_budget (x y : Fin n) (w : Lines n) (law : Legal w) :
    Legal (exchangeLines x y w) ∧ (exchangeLines x y w).card=w.card := by
  let s := Equiv.swap x y
  have ss (z : Fin n) : s (s z)=z := Equiv.swap_apply_self x y z
  have reverse (e : Fin n × Fin n) (h : e∈w) : exchangeLine x y (exchangeLine x y e)=e := by
    obtain ⟨a,b⟩ := e
    have ab : a<b := law _ h
    change ordered (s (ordered (s a,s b)).1,s (ordered (s a,s b)).2)=(a,b)
    by_cases le : s a≤s b
    · simp [ordered,le,ss,ab.le]
    · simp [ordered,le,ss,not_le_of_gt ab]
  constructor
  · intro e he
    obtain ⟨⟨a,b⟩,h,rfl⟩ := mem_image.mp he
    have ab : s a≠s b := s.injective.ne (law _ h).ne
    change (ordered (s a,s b)).1<(ordered (s a,s b)).2
    unfold ordered
    split
    · exact lt_of_le_of_ne ‹_› ab
    · exact lt_of_not_ge ‹_›
  · apply card_image_of_injOn
    intro a ha b hb eq
    exact (reverse a ha).symm.trans ((congrArg (exchangeLine x y) eq).trans (reverse b hb))

theorem touch_exchange (x y : Fin n) (w : Lines n) :
    Touch (exchangeLines x y w)=regrouped (Touch w) x y := by
  let s := Equiv.swap x y
  have ss (z : Fin n) : s (s z)=z := Equiv.swap_apply_self x y z
  funext a b
  apply propext
  have ends (e : Fin n × Fin n) : exchangeLine x y e=(a,b) ∨ exchangeLine x y e=(b,a) ↔
      e=(s a,s b) ∨ e=(s b,s a) := by
    obtain ⟨u,v⟩ := e
    rw [exchangeLine,unordered]
    have sEq (i j : Fin n) : s i=j ↔ i=s j := ⟨fun e => (ss i).symm.trans (congrArg s e),fun e => e ▸ ss j⟩
    change (s u=a ∧ s v=b) ∨ (s u=b ∧ s v=a) ↔ _
    simp only [sEq,Prod.mk.injEq]
  change (a,b)∈w.image _ ∨ (b,a)∈w.image _ ↔ (s a,s b)∈w ∨ (s b,s a)∈w
  constructor
  · intro h
    have get (e : Fin n × Fin n) (he : e∈w) (p : exchangeLine x y e=(a,b) ∨ exchangeLine x y e=(b,a)) :
        (s a,s b)∈w ∨ (s b,s a)∈w := by
      rcases (ends e).mp p with rfl|rfl
      · exact Or.inl he
      · exact Or.inr he
    rcases h with h|h <;> obtain ⟨e,he,z⟩ := mem_image.mp h
    · exact get e he (Or.inl z)
    · exact get e he (Or.inr z)
  · intro h
    have get (e : Fin n × Fin n) (he : e∈w) (p : e=(s a,s b) ∨ e=(s b,s a)) :
        (a,b)∈w.image (exchangeLine x y) ∨ (b,a)∈w.image (exchangeLine x y) := by
      rcases (ends e).mpr p with eq|eq
      · exact Or.inl (mem_image.mpr ⟨e,he,eq⟩)
      · exact Or.inr (mem_image.mpr ⟨e,he,eq⟩)
    exact h.elim (fun m => get _ m (Or.inl rfl)) (fun m => get _ m (Or.inr rfl))

theorem model_walk (g : Coloring (n+1) n) (w : Lines (n+1)) (c) (a b : Fin (n+1)) :
    Walk (WithMatching (Touch w) (mate g c)) a b ↔ Walk (Joined g w c) a b := by
  constructor <;> intro h <;> apply h.mapInto id
  · rintro x y (eq|wh|mh)
    · exact eq ▸ .stay _
    · exact .step (.stay _) (Or.inl wh)
    · exact .step (.stay _) (Or.inr (mh ▸ mate_spec g c x))
  · rintro x y (wh|⟨ne,col⟩)
    · exact .step (.stay _) (Or.inr (Or.inl wh))
    · exact .step (.stay _) (Or.inr (Or.inr
        (g.proper _ _ _ (mate_spec g c x).1 ne ((mate_spec g c x).2.trans col.symm))))

theorem model_connected (g : Coloring (n+1) n) (w : Lines (n+1)) (c) :
    Connected (WithMatching (Touch w) (mate g c)) ↔ Connected (Joined g w c) :=
  ⟨fun h x y => (model_walk g w c x y).mp (h x y),fun h x y => (model_walk g w c x y).mpr (h x y)⟩

def keeps {V : Type} (W : V → V → Prop) (m : V → V) (x y : V) : Prop :=
  m x=y ∨ Walk (Remainder W m x y) x (m x) ∨ Walk (Remainder W m x y) x y ∨
  Walk (Remainder W m x y) (m y) (m x) ∨ Walk (Remainder W m x y) (m y) y

/-- An end-to-end test on the given wild lines and coloring. It covers
every other color as well as the one that initially has two components. -/
theorem exchange_works_iff (g : Coloring (n+1) n) (w : Lines (n+1)) (c : Fin n) (x y : Fin (n+1))
    (cover : ∀ v,Walk (Joined g w c) v x ∨ Walk (Joined g w c) v y)
    (apart : ¬Walk (Joined g w c) x y)
    (rest : ∀ d,d≠c → Connected (Joined g w d)) :
    Works g (exchangeLines x y w) ↔
      (Walk (Remainder (Touch w) (mate g c) x y) x (mate g c x) ∨
       Walk (Remainder (Touch w) (mate g c) x y) y (mate g c y)) ∧
      ∀ d,d≠c → keeps (Touch w) (mate g d) x y := by
  have sym : ∀ {a b},Touch w a b → Touch w b a := fun h => h.symm
  have test (d : Fin n) := (model_connected g (exchangeLines x y w) d).symm
  simp only [touch_exchange] at test
  have failed := (test c).trans (repair_two_components (Touch w) sym (mate g c) (mate_involutive _ _)
    (fun a => (mate_spec _ _ a).1) x y (fun v => (cover v).imp (model_walk _ _ _ _ _).mpr (model_walk _ _ _ _ _).mpr)
      (fun h => apart ((model_walk _ _ _ _ _).mp h)))
  have others (d : Fin n) (ne : d≠c) : Connected (Joined g (exchangeLines x y w) d) ↔ keeps (Touch w) (mate g d) x y :=
    (test d).trans (retain_color _ sym _ (mate_involutive _ _) (fun a => (mate_spec _ _ a).1) x y
      ((model_connected _ _ d).mpr (rest d ne)))
  constructor
  · exact fun h => ⟨failed.mp (h c),fun d ne => (others d ne).mp (h d)⟩
  · intro h d
    by_cases eq : d=c
    · exact eq ▸ failed.mpr h.1
    · exact (others d eq).mpr (h.2 d eq)

#print axioms exchange_works_iff
#print axioms same_budget
end WildExact.Regroup.Switch
