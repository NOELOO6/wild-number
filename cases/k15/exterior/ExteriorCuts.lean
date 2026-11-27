import ExteriorPorts
namespace WildExterior
open Finset WildSieve

private theorem root_blocked (F : Factor V Color) (i : Port ↪ V) (r : V) (out : r∉outside i)
    (c : Color) (T : Finset Port) (three : T.card=3) (cl : Closed (F.f c) (insert r (T.map i))) :
    T∈rootTriples (ordinary F i c) (tap F i r c) := by
  have into := cl r (mem_insert_self _ _)
  have tr := (mem_insert.mp into).resolve_left (F.moving c r).symm
  obtain ⟨x,xt,eq⟩ := mem_map.mp tr
  have tx := (tap_spec F i r c x).mpr eq
  have someX : tap F i r c=some x := by
    cases e : tap F i r c with
    | none => simp [star,e] at tx
    | some y =>
      have xy : x=y := by simpa [star,e] using tx
      rw [xy]
  have q : T.erase x∈ordinary F i c := by
    apply ordinary_mem.mpr
    refine ⟨by rw [card_erase_of_mem xt,three],?_⟩
    intro v hv
    obtain ⟨z,hz,rfl⟩ := mem_map.mp hv
    have s := cl (i z) (mem_insert_of_mem (mem_map.mpr ⟨z,(mem_erase.mp hz).2,rfl⟩))
    have no : F.f c (i z)≠r := by
      intro e
      have ze : i z=F.f c r := (F.invol c (i z)).symm.trans (congrArg (F.f c) e)
      exact (mem_erase.mp hz).1 (i.injective (ze.trans eq.symm))
    obtain ⟨y,yt,ey⟩ := mem_map.mp ((mem_insert.mp s).resolve_left no)
    have yx : y≠x := by
      intro e
      have same : F.f c (i z)=F.f c r := ey.symm.trans ((congrArg i e).trans eq)
      exact out ((F.invol c).injective same ▸ port_inside i z)
    exact mem_map.mpr ⟨y,mem_erase.mpr ⟨yx,yt⟩,ey⟩
  rw [someX,rootTriples]
  exact mem_image.mpr ⟨_,q,insert_erase xt⟩

private theorem outer_six (F : Factor V Color) (i : Port ↪ V) (c : Color) (T : Finset Port)
    (three : T.card=3) (cap : (ordinary F i c).card≤3) (cl : Closed (F.f c) (outside i \ T.map i)) :
    T=(used (ordinary F i c))ᶜ ∧ (ordinary F i c).card=3 := by
  let p := ordinary F i c
  have sub : Tᶜ⊆used p := by
    intro x hx
    apply (inside_partners F i c x).mpr
    have nx : i x∉T.map i := by simpa using mem_compl.mp hx
    exact (mem_sdiff.mp (cl (i x) (mem_sdiff.mpr ⟨port_inside i x,nx⟩))).1
  have sz := (ordinary_counts F i c).1
  change (used p).card=2*p.card at sz
  have tc : Tᶜ.card=6 := by rw [card_compl,Fintype.card_fin,three]
  have le := card_le_card sub
  change p.card≤3 at cap
  have eq := eq_of_subset_of_card_le sub (by omega)
  change T=(used p)ᶜ ∧ p.card=3
  exact ⟨by simpa using congrArg (fun s : Finset Port => sᶜ) eq,by omega⟩

theorem common_cuts (F : Factor V Color) (i : Port ↪ V) (r : V) (out : r∉outside i)
    (cap : ∀ c,(ordinary F i c).card≤3) (T : Finset Port) (sz : T.card=3)
    (pass : T∉rejected (ordinary F i) (tap F i r)) (c : Color) :
    ¬Closed (F.f c) (insert r (T.map i)) ∧ ¬Closed (F.f c) (outside i \ T.map i) := by
  have no : T∉blocked (ordinary F i c) (tap F i r c) :=
    fun h => pass (mem_biUnion.mpr ⟨c,mem_univ _,h⟩)
  constructor
  · intro cl
    have mem := root_blocked F i r out c T sz cl
    apply no
    unfold blocked
    split
    · exact mem_insert_of_mem mem
    · exact mem
  · intro cl
    obtain ⟨eq,sz⟩ := outer_six F i c T sz (cap c) cl
    exact no (by simp [blocked,sz,eq])
end WildExterior
