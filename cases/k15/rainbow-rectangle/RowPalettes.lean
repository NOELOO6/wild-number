import ColumnCount
import SevenSets

namespace WildRectangle
open Finset
variable {V C : Type} [DecidableEq V] [DecidableEq C]

/-- A Latin square presented by its row permutations. -/
structure Rows (V C : Type) where
  row : V → (V ≃ C)
  column : ∀ x,Function.Injective (fun a => row a x)

def palette (L : Rows V C) (A : Finset V) (x : V) := A.image (fun a => L.row a x)
def transition (L : Rows V C) (a b : V) := (L.row a).trans (L.row b).symm

def Rectangle (L : Rows V C) (A S : Finset V) :=
  ∃ B⊆S,B.card=3 ∧ (B : Set V).PairwiseDisjoint (palette L A)

def rowSet [Fintype V] (L : Rows V C) (a : V) (X : Finset V) :=
  univ.filter fun d => X.image (L.row d)=X.image (L.row a)

private theorem inverse_cols (L : Rows V C) (A : Finset V) (c : C) (x : V) :
    c∈palette L A x ↔ x∈A.image (fun a => (L.row a).symm c) := by
  constructor
  · rintro h
    obtain ⟨d,hd,h⟩ := mem_image.mp h
    exact mem_image.mpr ⟨d,hd,(L.row d).symm_apply_eq.mpr h.symm⟩
  · intro h
    obtain ⟨d,hd,rfl⟩ := mem_image.mp h
    exact mem_image.mpr ⟨d,hd,(L.row d).apply_symm_apply c⟩

variable [Fintype V]

/-- A third row which fails to supply a rainbow rectangle must share a
seven-color palette with both prescribed rows on the same seven columns. -/
theorem rectangle_or_seven (L : Rows V C) (a b d : V) (ab : a≠b) (A S U : Finset V)
    (aa : a∈A) (bb : b∈A) (dd : d∈A) (asize : A.card=3) (size : 12≤S.card) (su : S⊆U)
    (special : ∃ x∈S,∃ c∈palette L A x,∀ y∈S,c∈palette L A y → y=x) :
    Rectangle L A S ∨ ∃ Y,Seven (transition L a b) U Y ∧ a∈rowSet L a Y ∧ b∈rowSet L a Y ∧ d∈rowSet L a Y := by
  classical
  by_cases ok : Rectangle L A S
  · exact Or.inl ok
  right
  let P := palette L A
  obtain ⟨x,xs,c,cx,only⟩ := special
  have sz (v) : (P v).card=3 := (card_image_of_injective _ (L.column v)).trans asize
  have sub (T : Finset V) (k : C) : T.filter (fun y => k∈P y)⊆A.image (fun a => (L.row a).symm k) :=
    fun y hy => (inverse_cols _ _ _ _).mp (mem_filter.mp hy).2
  have freq (T : Finset V) (k) : (T.filter fun y => k∈P y).card≤3 :=
    (card_le_card (sub T k)).trans (card_image_le.trans asize.le)
  let Y := (S.erase x).filter (fun y => Disjoint (P x) (P y))
  have sy : Y⊆S := (filter_subset _ _).trans (erase_subset _ _)
  have seven : 7≤Y.card := companions P S size x xs (sz x) (freq S) c cx only
  have meet (y) (yy : y∈Y) (z) (zz : z∈Y) (ne : y≠z) : (P y∩P z).Nonempty := by
    by_contra! h
    have xy := mem_filter.mp yy
    have xz := mem_filter.mp zz
    have xn : x≠y := (mem_erase.mp xy.1).1.symm
    have xz' : x≠z := (mem_erase.mp xz.1).1.symm
    have yz : Disjoint (P y) (P z) := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h)
    apply ok
    refine ⟨{x,y,z},insert_subset xs (insert_subset (sy yy) (singleton_subset_iff.mpr (sy zz))),by simp [xn,xz',ne],?_⟩
    intro u hu v hv uv
    simp only [coe_insert,coe_singleton,Set.mem_insert_iff,Set.mem_singleton_iff] at hu hv
    rcases hu with rfl|rfl|rfl <;> rcases hv with rfl|rfl|rfl <;>
      first | exact False.elim (uv rfl) | exact xy.2 | exact xz.2 | exact yz | exact xy.2.symm | exact xz.2.symm | exact yz.symm
  have tight (y) (hy : y∈Y) := tight_columns P Y seven (fun v _ => sz v) (freq Y) meet y hy
  obtain ⟨v,hv⟩ := card_pos.mp (by omega : 0<Y.card)
  have full (y) (hy : y∈Y) (k) (ky : k∈P y) :
      Y.filter (fun u => k∈P u)=A.image (fun a => (L.row a).symm k) := by
    apply eq_of_subset_of_card_le (sub Y k) _
    rw [(tight y hy).2.1 k ky]
    exact card_image_le.trans asize.le
  have across (v) (av : v∈A) (w) (aw : w∈A) (y) (hy : y∈Y) :
      (L.row w).symm (L.row v y)∈Y := by
    have pal : L.row v y∈P y := mem_image.mpr ⟨v,av,rfl⟩
    exact (mem_filter.mp ((full y hy _ pal).symm ▸
      (show (L.row w).symm (L.row v y)∈A.image (fun a => (L.row a).symm (L.row v y)) from mem_image.mpr ⟨w,aw,rfl⟩))).1
  have same (v) (av : v∈A) : v∈rowSet L a Y := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,eq_of_subset_of_card_le ?_ (by rw [card_image_of_injective _ (L.row a).injective,card_image_of_injective _ (L.row v).injective])⟩
    intro k kh
    obtain ⟨y,hy,rfl⟩ := mem_image.mp kh
    exact mem_image.mpr ⟨_,across v av a aa y hy,(L.row a).apply_symm_apply _⟩
  let p := transition L a b
  have stable : Stable p Y := by
    intro y
    constructor
    · intro h
      have old := across b bb a aa (p y) h
      simpa [p,transition] using old
    · exact across a aa b bb y
  have long (y) (hy : y∈Y) : p (p y)≠y := by
    intro tw
    have py := (stable y).mpr hy
    have eq (w) : L.row b (p w)=L.row a w := (L.row b).apply_symm_apply _
    have diff := (L.column y).ne ab
    have yp : y≠p y := fun e => diff ((eq y).symm.trans (congrArg (L.row b) e.symm))
    have eq' : L.row a (p y)=L.row b y := by rw [←eq (p y),tw]
    have common : ({L.row a y,L.row b y} : Finset C)⊆P y∩P (p y) := by
      apply insert_subset
      · exact mem_inter.mpr ⟨mem_image.mpr ⟨a,aa,rfl⟩,mem_image.mpr ⟨b,bb,eq y⟩⟩
      · exact singleton_subset_iff.mpr (mem_inter.mpr ⟨mem_image.mpr ⟨b,bb,rfl⟩,mem_image.mpr ⟨a,aa,eq'⟩⟩)
    have cnt := card_le_card common
    rw [(tight y hy).2.2 _ py yp.symm] at cnt
    simp [diff] at cnt
  exact ⟨Y,⟨sy.trans su,(tight v hv).1,stable,long⟩,same a aa,same b bb,same d dd⟩
end WildRectangle
