import RedrawRows
namespace SearchRedraw
open EdgeWalk WildDeletion
def erasedKey (mask : Nat) := SearchExample.rows.zipIdx.foldl
  (fun bits (m,c) => if mask.testBit c then bits ||| mkKey (original m) else bits) 0
theorem valid_pivots : plans.all (fun p => p.pivot==0 || (erasedKey p.mask).testBit (p.pivot-1)) = true := by
  native_decide

def Good (w : Edges) (actual : List Item) := w.length=10 ∧ w.Nodup ∧ (∀ e∈w,e.1<e.2) ∧
  (∀ m∈old, Connected (Adj (w++m))) ∧ ∀ m∈actual, Connected (Adj (w++m.edges))

private theorem works {actual : List Item} (i : Nat) (h : base i = true)
    (newPaths : ∀ m∈actual, passes 0 (wild i++m.edges)=true) : Good (wild i) actual := by
  obtain ⟨legal,paths⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨len,unique,order⟩ := of_decide_eq_true legal
  exact ⟨len,unique,order,fun m hm => connected_of_passes 0 _ (List.all_eq_true.mp paths m hm),
    fun m hm => connected_of_passes 0 _ (newPaths m hm)⟩

private theorem stored_ids : plans.all (fun p => p.ids.all p.ids.eraseDups.contains) = true := by native_decide

theorem graph_repair (p : Plan) (listed : p∈plans) (actual : List Item)
    (allowed : ∀ m∈actual, m∈pool p.mask)
    (proper : ∀ a∈actual, ∀ b∈actual, compatible a b = true)
    (covers : ∀ i, (erasedKey p.mask).testBit i = true → ∃ m∈actual, m.key.testBit i = true) :
    ∃ w, Good w actual := by
  have cert := List.all_eq_true.mp every_certificate p listed
  unfold ok at cert
  split at cert
  · obtain ⟨baseOK,empty⟩ := Bool.and_eq_true_iff.mp cert
    refine ⟨_,works _ baseOK (fun m hm => ?_)⟩
    by_cases yes : passes 0 (wild (p.ids.headD 0)++m.edges)=true
    · exact yes
    have hn : passes 0 (wild (p.ids.headD 0)++m.edges)=false := Bool.eq_false_iff.mpr yes
    have bad : m ∈ broken (pool p.mask) (p.ids.headD 0) := List.mem_filter.mpr ⟨allowed m hm,by rw [hn]; rfl⟩
    rw [List.isEmpty_iff.mp empty] at bad
    exact (List.not_mem_nil bad).elim
  · rename_i branch
    obtain ⟨front,byId⟩ := Bool.and_eq_true_iff.mp cert
    obtain ⟨_,len⟩ := Bool.and_eq_true_iff.mp front
    have pivot := List.all_eq_true.mp valid_pivots p listed
    have yes : (erasedKey p.mask).testBit (p.pivot-1) = true := by
      simpa [show p.pivot ≠ 0 by simpa using branch] using pivot
    obtain ⟨a,ha,hp⟩ := covers _ yes
    have inA : a ∈ anchors p (pool p.mask) := List.mem_filter.mpr ⟨allowed a ha,hp⟩
    have eq : (anchors p (pool p.mask)).length = p.ids.length := beq_iff_eq.mp len
    rw [←List.map_fst_zip (l₂:=p.ids) (Nat.le_of_eq eq)] at inA
    obtain ⟨⟨b,i⟩,row,same⟩ := List.mem_map.mp inA
    change b=a at same
    subst b
    have memId := List.of_mem_zip row
    have checked := List.all_eq_true.mp byId i (List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp stored_ids p listed) i memId.2))
    obtain ⟨baseOK,permit⟩ := Bool.and_eq_true_iff.mp checked
    have okPair := List.all_eq_true.mp permit (a,i) row
    have excludes : (broken (pool p.mask) i).all (fun b => !compatible a b) = true := by simpa using okPair
    refine ⟨_,works i baseOK (fun m hm => ?_)⟩
    by_cases yes : passes 0 (wild i++m.edges)=true
    · exact yes
    have hn : passes 0 (wild i++m.edges)=false := Bool.eq_false_iff.mpr yes
    have bad : m ∈ broken (pool p.mask) i := List.mem_filter.mpr ⟨allowed m hm,by rw [hn]; rfl⟩
    have no := List.all_eq_true.mp excludes m bad
    simp [proper a ha m hm] at no

/-- Any collection of perfect matchings on the six erased colors that
covers the erased edges and is pairwise edge-disjoint has a common solution. -/
theorem actual_redraw (p : Plan) (listed : p∈plans) (actual : List Raw)
    (allowed : ∀ m∈actual, Allowed p.mask points m ∧ m.length=8)
    (proper : ∀ a∈actual, ∀ b∈actual, a=b ∨ mkKey a &&& mkKey b=0)
    (covers : ∀ i, (erasedKey p.mask).testBit i=true → ∃ m∈actual, (mkKey m).testBit i=true) :
    ∃ w : Edges, w.length=10 ∧ w.Nodup ∧ (∀ e∈w,e.1<e.2) ∧
      ∀ m∈old ++ actual.map erase, Connected (Adj (w++m)) := by
  obtain ⟨w,len,unique,legal,orig,fresh⟩ := graph_repair p listed (actual.map item)
    (fun m hm => by
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hm
      obtain ⟨hit,sz⟩ := allowed u hu
      exact List.mem_map_of_mem (exhaustive hit 8 (Nat.le_of_eq sz)))
    (fun a ha b hb => by
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
      rcases proper x hx y hy with rfl | h <;> simp_all [compatible,item])
    (fun i hi => by
      obtain ⟨m,hm,h⟩ := covers i hi
      exact ⟨item m,List.mem_map_of_mem hm,h⟩)
  refine ⟨w,len,unique,legal,fun m hm => ?_⟩
  rcases List.mem_append.mp hm with h|h
  · exact orig m h
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
    exact fresh (item u) (List.mem_map_of_mem hu)
#print axioms actual_redraw
end SearchRedraw
