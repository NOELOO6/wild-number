import GraphSwitch
import StarDraw
namespace WildExact.Regroup.Switch
open Finset WildDeletion WildSieve
variable {n : Nat}

private theorem lift_pair (w : Lines n) {a b : Fin (n+1)} (h : Touch (w.map liftLine) a b) :
    ∃ u v : Fin n,a=u.castSucc ∧ b=v.castSucc ∧ Touch w u v := by
  rcases h with h|h
  · obtain ⟨⟨u,v⟩,old,e⟩ := mem_map.mp h
    exact ⟨u,v,(congrArg Prod.fst e).symm,(congrArg Prod.snd e).symm,Or.inl old⟩
  · obtain ⟨⟨u,v⟩,old,e⟩ := mem_map.mp h
    exact ⟨v,u,(congrArg Prod.snd e).symm,(congrArg Prod.fst e).symm,Or.inr old⟩

private theorem embed_walk (g : Coloring n n) (odd : n%2=1) (w : Lines n) (c)
    {a b : Fin n} (h : Walk (Joined g w c) a b) :
    Walk (Joined (augment odd g) (w.map liftLine) c) a.castSucc b.castSucc := by
  apply h.mapInto Fin.castSucc
  rintro u v ((e|e)|⟨ne,col⟩)
  · exact .step (.stay _) (Or.inl (Or.inl (mem_map.mpr ⟨_,e,rfl⟩)))
  · exact .step (.stay _) (Or.inl (Or.inr (mem_map.mpr ⟨_,e,rfl⟩)))
  · exact .step (.stay _) (Or.inr ⟨fun e => ne (Fin.castSucc_injective _ e),by rwa [augment_paint]⟩)

/-- The added root is a leaf in each color projection. Deleting it preserves
all ordinary paths, including paths after a redraw. -/
theorem project_color (g : Coloring n n) (odd : n%2=1) (w : Lines n) (c : Fin n) :
    ∃ q : Fin (n+1) → Fin n,(∀ a,q a.castSucc=a) ∧
      ∀ a b,Walk (Joined (augment odd g) (w.map liftLine) c) a b ↔ Walk (Joined g w c) (q a) (q b) := by
  let G := augment odd g
  let r := Fin.last n
  obtain ⟨p,ep⟩ := before_root (mate G c r) (mate_spec G c r).1.symm
  let q : Fin (n+1) → Fin n := Fin.lastCases p id
  have qr : q r=p := Fin.lastCases_last
  have qo (v : Fin n) : q v.castSucc=v := Fin.lastCases_castSucc _
  have leaf : Joined G (w.map liftLine) c r p.castSucc := Or.inr (ep ▸ mate_spec G c r)
  have root_edge (v : Fin n) (e : Joined G (w.map liftLine) c r v.castSucc) : p=v := by
    rcases e with wild|⟨ne,col⟩
    · obtain ⟨u,_,eq,_,_⟩ := lift_pair w wild
      exact (Fin.castSucc_ne_last u eq.symm).elim
    · apply Fin.castSucc_injective n
      rw [ep]
      exact G.proper _ _ _ (mate_spec G c r).1 ne ((mate_spec G c r).2.trans col.symm)
  have project (a b : Fin (n+1)) (e : Joined G (w.map liftLine) c a b) : Walk (Joined g w c) (q a) (q b) := by
    cases a using Fin.lastCases with
    | last =>
      cases b using Fin.lastCases with
      | last => exact .stay _
      | cast v => rw [qr,qo,root_edge v e];exact .stay _
    | cast u =>
      cases b using Fin.lastCases with
      | last => rw [qr,qo,root_edge u (joined_symm G e)];exact .stay _
      | cast v =>
        rw [qo,qo]
        rcases e with he|⟨ne,col⟩
        · obtain ⟨a,b,eq₁,eq₂,wh⟩ := lift_pair w he
          exact .step (.stay _) (Or.inl ((Fin.castSucc_inj.mp eq₁) ▸ (Fin.castSucc_inj.mp eq₂) ▸ wh))
        · exact .step (.stay _) (Or.inr ⟨fun h => ne (congrArg Fin.castSucc h),by simpa [G] using col⟩)
  have near (a : Fin (n+1)) : Walk (Joined G (w.map liftLine) c) a (q a).castSucc := by
    cases a using Fin.lastCases with
    | last => rw [qr];exact .step (.stay _) leaf
    | cast v => rw [qo];exact .stay _
  refine ⟨q,qo,fun a b => ⟨Walk.mapInto q project,?_⟩⟩
  intro h
  exact ((near a).join (embed_walk g odd w c h)).join (backwards (joined_symm _) (near b))

private theorem lift_exchange (x y : Fin n) (w : Lines n) :
    (exchangeLines x y w).map liftLine=exchangeLines x.castSucc y.castSucc (w.map liftLine) := by
  have point (v : Fin n) : (Equiv.swap x y v).castSucc=Equiv.swap x.castSucc y.castSucc v.castSucc := by
    by_cases a : v=x
    · subst v;simp
    by_cases b : v=y
    · subst v;simp
    simp [Equiv.swap_apply_of_ne_of_ne,a,b,Fin.castSucc_injective n |>.ne a,Fin.castSucc_injective n |>.ne b]
  have one (a : Fin n × Fin n) :
      liftLine (exchangeLine x y a)=exchangeLine x.castSucc y.castSucc (liftLine a) := by
    obtain ⟨u,v⟩ := a
    let s := Equiv.swap x y
    change liftLine (WildCuts.ordered (s u,s v))=WildCuts.ordered (Equiv.swap _ _ u.castSucc,Equiv.swap _ _ v.castSucc)
    rw [←point,←point]
    by_cases le : s u≤s v
    · have ll : (s u).castSucc≤(s v).castSucc := le
      simp [WildCuts.ordered,le,ll,s];rfl
    · have ll : ¬(s u).castSucc≤(s v).castSucc := le
      simp [WildCuts.ordered,le,ll,s];rfl
  ext e
  simp only [exchangeLines,mem_map,mem_image]
  constructor
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨liftLine a,⟨a,ha,rfl⟩,(one a).symm⟩
  · rintro ⟨_,⟨a,ha,rfl⟩,rfl⟩
    exact ⟨exchangeLine x y a,⟨a,ha,rfl⟩,one a⟩

private theorem lift_connected (g : Coloring n n) (odd : n%2=1) (w : Lines n) (c) :
    Connected (Joined (augment odd g) (w.map liftLine) c) ↔ Connected (Joined g w c) := by
  obtain ⟨q,old,path⟩ := project_color g odd w c
  refine ⟨fun h a b => ?_,fun h a b => (path a b).mpr (h _ _)⟩
  simpa only [old] using (path _ _).mp (h a.castSucc b.castSucc)

/-- The same swap test applies to the original odd graph. Both exchanged
points are ordinary; the extra root stays fixed and carries no wild edge. -/
theorem odd_exchange_works_iff (g : Coloring n n) (odd : n%2=1) (w : Lines n) (c : Fin n) (x y : Fin n)
    (cover : ∀ v,Walk (Joined g w c) v x ∨ Walk (Joined g w c) v y)
    (apart : ¬Walk (Joined g w c) x y)
    (rest : ∀ d,d≠c → Connected (Joined g w d)) :
    let W := Touch (w.map liftLine)
    let f := mate (augment odd g)
    let a := x.castSucc
    let b := y.castSucc
    Works g (exchangeLines x y w) ↔
      (Walk (Remainder W (f c) a b) a (f c a) ∨ Walk (Remainder W (f c) a b) b (f c b)) ∧
      ∀ d,d≠c → keeps W (f d) a b := by
  let G := augment odd g
  obtain ⟨q,onOld,path⟩ := project_color g odd w c
  have each (v) := cover (q v)
  have all (v) : Walk (Joined G (w.map liftLine) c) v x.castSucc ∨ Walk (Joined G (w.map liftLine) c) v y.castSucc := by
    rcases each v with l|r
    · exact Or.inl ((path _ _).mpr (by rwa [onOld]))
    · exact Or.inr ((path _ _).mpr (by rwa [onOld]))
  have part : ¬Walk (Joined G (w.map liftLine) c) x.castSucc y.castSucc := fun h =>
    apart (by simpa only [onOld] using (path _ _).mp h)
  have exactTest := exchange_works_iff G (w.map liftLine) c x.castSucc y.castSucc all part
    (fun d ne => (lift_connected g odd w d).mpr (rest d ne))
  rw [←lift_exchange] at exactTest
  refine Iff.trans ?_ exactTest
  exact ⟨fun h d => (lift_connected g odd _ d).mpr (h d),fun h d => (lift_connected g odd _ d).mp (h d)⟩

#print axioms odd_exchange_works_iff
end WildExact.Regroup.Switch
