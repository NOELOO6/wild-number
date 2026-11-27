import BridgeSwitch
namespace WildExact.Regroup.Switch
open WildDeletion
variable {V : Type} [DecidableEq V]

def ends (m : V → V) (x y : V) (i : Fin 4) : V :=
  if i=0 then x else if i=1 then m x else if i=2 then y else m y

/-- Allow staying at a vertex so pairing two equal ports has its usual
reachability meaning. -/
def WithMatching (W : V → V → Prop) (m : V → V) (a b : V) := a=b ∨ W a b ∨ m a=b

def Remainder (W : V → V → Prop) (m : V → V) (x y a b : V) :=
  a=b ∨ W a b ∨ (∀ i : Fin 4,a≠ends m x y i) ∧ m a=b

def regrouped (W : V → V → Prop) (x y : V) (a b : V) := W (Equiv.swap x y a) (Equiv.swap x y b)

private def oldMate (i : Fin 4) : Fin 4 := if i=0 then 1 else if i=1 then 0 else if i=2 then 3 else 2
private def newMate (i : Fin 4) : Fin 4 := if i=0 then 3 else if i=1 then 2 else if i=2 then 1 else 0

omit [DecidableEq V] in
private theorem on_edge (m : V → V) (inv : Function.Involutive m) (x y : V) (i : Fin 4) :
    m (ends m x y i)=ends m x y (oldMate i) := by
  have cases4 : ∀ i : Fin 4,i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
  rcases cases4 i with rfl|rfl|rfl|rfl <;> simp [ends,oldMate,inv x,inv y]

private theorem unchanged (m : V → V) (inv : Function.Involutive m) (x y a : V)
    (away : ∀ i,a≠ends m x y i) :
    Equiv.swap x y (m (Equiv.swap x y a))=m a := by
  have ax : a≠x := away 0
  have ay : a≠y := away 2
  have mx : m a≠x := fun e => away 1 ((inv a).symm.trans (congrArg m e))
  have my : m a≠y := fun e => away 3 ((inv a).symm.trans (congrArg m e))
  rw [Equiv.swap_apply_of_ne_of_ne ax ay,Equiv.swap_apply_of_ne_of_ne mx my]

private theorem switched_edge (m : V → V) (inv : Function.Involutive m) (free : ∀ a,a≠m a)
    (x y : V) (different : m x≠y) (i : Fin 4) :
    Equiv.swap x y (m (Equiv.swap x y (ends m x y i)))=ends m x y (newMate i) := by
  have yx : m y≠x := fun e => different ((congrArg m e).symm.trans (inv y))
  have aa := Equiv.swap_apply_of_ne_of_ne (free x).symm different
  have bb := Equiv.swap_apply_of_ne_of_ne yx (free y).symm
  have cases4 : ∀ i : Fin 4,i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by decide
  rcases cases4 i with rfl|rfl|rfl|rfl <;> simp [ends,newMate,aa,bb,inv x,inv y]

omit [DecidableEq V] in
theorem remainder_sym (W : V → V → Prop) (sym : ∀ {a b},W a b → W b a)
    (m : V → V) (inv : Function.Involutive m) (x y : V) :
    ∀ {a b},Remainder W m x y a b → Remainder W m x y b a := by
  rintro a b (eq|w|⟨away,mb⟩)
  · exact Or.inl eq.symm
  · exact Or.inr (Or.inl (sym w))
  · subst b
    refine Or.inr (Or.inr ⟨fun i e => away (oldMate i) ?_,inv a⟩)
    exact (inv a).symm.trans ((congrArg m e).trans (on_edge m inv x y i))

private theorem rebuild (W : V → V → Prop) (m f : V → V) (x y : V) (side : Fin 4 → Bool)
    (other : Fin 4 → Fin 4) (partner : ∀ i,f (ends m x y i)=ends m x y (other i))
    (pair : ∀ i j,side i=side j ↔ i=j ∨ other i=j)
    (rest : ∀ a,(∀ i,a≠ends m x y i) → f a=m a) :
    Draw (Remainder W m x y) (ends m x y) side=WithMatching W f := by
  classical
  funext a b
  apply propext
  constructor
  · rintro ((eq|edge|⟨away,mb⟩)|⟨i,j,rfl,rfl,same⟩)
    · exact Or.inl eq
    · exact Or.inr (Or.inl edge)
    · exact Or.inr (Or.inr ((rest a away).trans mb))
    · rcases (pair i j).mp same with rfl|e
      · exact Or.inl rfl
      · exact Or.inr (Or.inr ((partner i).trans (congrArg (ends m x y) e)))
  · rintro (eq|edge|matchEdge)
    · exact Or.inl (Or.inl eq)
    · exact Or.inl (Or.inr (Or.inl edge))
    · by_cases atPort : ∃ i,a=ends m x y i
      · obtain ⟨i,rfl⟩ := atPort
        exact Or.inr ⟨i,other i,rfl,matchEdge.symm.trans (partner i),(pair i _).mpr (Or.inr rfl)⟩
      · have away : ∀ i,a≠ends m x y i := fun i e => atPort ⟨i,e⟩
        exact Or.inl (Or.inr (Or.inr ⟨away,(rest a away).symm.trans matchEdge⟩))

private theorem redraw_iff (W : V → V → Prop) (m : V → V) (x y : V) :
    Connected (WithMatching (regrouped W x y) m) ↔
      Connected (WithMatching W (fun a => Equiv.swap x y (m (Equiv.swap x y a)))) := by
  let s := Equiv.swap x y
  have ss (v : V) : s (s v)=v := Equiv.swap_apply_self x y v
  constructor <;> intro h a b <;> have path := h (s a) (s b)
  · rw [←ss a,←ss b]
    apply path.mapInto s
    rintro u v (eq|e|e)
    · exact eq ▸ .stay _
    · exact .step (.stay _) (Or.inr (Or.inl e))
    · exact .step (.stay _) (Or.inr (Or.inr (by change s (m (s (s u)))=s v;rw [ss,e])))
  · rw [←ss a,←ss b]
    apply path.mapInto s
    rintro u v (eq|e|e)
    · exact eq ▸ .stay _
    · exact .step (.stay _) (Or.inr (Or.inl (by change W (s (s u)) (s (s v));rwa [ss,ss])))
    · exact .step (.stay _) (Or.inr (Or.inr (by change s (m (s u))=v at e;rw [←e,ss])))

/-- Exchange x and y between their wild groups in a perfect matching.
If these points lie in the two different components of this color, the
exchange succeeds exactly when one old matching edge has a detour. -/
theorem repair_two_components (W : V → V → Prop) (sym : ∀ {a b},W a b → W b a)
    (m : V → V) (inv : Function.Involutive m) (free : ∀ a,a≠m a) (x y : V)
    (cover : ∀ v,Walk (WithMatching W m) v x ∨ Walk (WithMatching W m) v y)
    (apart : ¬Walk (WithMatching W m) x y) :
    Connected (WithMatching (regrouped W x y) m) ↔
      Walk (Remainder W m x y) x (m x) ∨ Walk (Remainder W m x y) y (m y) := by
  have diff : m x≠y := fun e => apart (.step (.stay _) (Or.inr (Or.inr e)))
  have old := rebuild W m m x y before oldMate (on_edge m inv x y) (by decide) (fun _ _ => rfl)
  have new := rebuild W m _ x y after newMate (switched_edge m inv free x y diff) (by decide) (unchanged m inv x y)
  rw [redraw_iff,←new]
  apply two_parts _ _ (remainder_sym W sym m inv x y)
  · rw [old];exact cover
  · rw [old];exact apart

/-- For a color that already connects the graph, the analogous four paths
give a test for retaining that color. If x and y are partners, exchanging
them preserves connectivity automatically. -/
theorem retain_color (W : V → V → Prop) (sym : ∀ {a b},W a b → W b a)
    (m : V → V) (inv : Function.Involutive m) (free : ∀ a,a≠m a) (x y : V)
    (oldConn : Connected (WithMatching W m)) :
    Connected (WithMatching (regrouped W x y) m) ↔ m x=y ∨
      Walk (Remainder W m x y) x (m x) ∨ Walk (Remainder W m x y) x y ∨
      Walk (Remainder W m x y) (m y) (m x) ∨ Walk (Remainder W m x y) (m y) y := by
  rw [redraw_iff]
  by_cases matchEdge : m x=y
  · have mx : m y=x := matchEdge ▸ inv x
    have same : (fun a => Equiv.swap x y (m (Equiv.swap x y a)))=m := by
      funext a
      by_cases ax : a=x
      · subst a;simp [matchEdge,mx]
      by_cases ay : a=y
      · subst a;simp [matchEdge,mx]
      have neX : m a≠x := fun e => ay (inv.injective (e.trans mx.symm))
      have neY : m a≠y := fun e => ax (inv.injective (e.trans matchEdge.symm))
      rw [Equiv.swap_apply_of_ne_of_ne ax ay,Equiv.swap_apply_of_ne_of_ne neX neY]
    rw [same]
    exact ⟨fun _ => Or.inl matchEdge,fun _ => oldConn⟩
  · have old := rebuild W m m x y before oldMate (on_edge m inv x y) (by decide) (fun _ _ => rfl)
    have new := rebuild W m _ x y after newMate (switched_edge m inv free x y matchEdge) (by decide) (unchanged m inv x y)
    rw [←new,or_iff_right matchEdge]
    apply keep_connected _ _ (remainder_sym W sym m inv x y)
    rwa [old]

#print axioms retain_color
#print axioms repair_two_components
end WildExact.Regroup.Switch
