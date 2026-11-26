import RedrawSound
namespace InsideNames
open VertexRedraw EdgeWalk WildDeletion RedrawModel

abbrev Injective {α β : Type} (f : α→β) := ∀ ⦃x y⦄, f x=f y → x=y
abbrev Surjective {α β : Type} (f : α→β) := ∀ y, ∃ x, f x=y

def rename (p : List (Fin 6)) (x : C) : C :=
  if x.val<6 then ⟨p[x.val]!.val,by have := p[x.val]!.isLt; omega⟩ else x
def works (p : List (Fin 6)) (a b : List Nat) := (trial a).all fun (x,y) =>
  (run (trial b) 15 (2^(rename p x).val)).testBit (rename p y).val
set_option maxRecDepth 10000
theorem starts_move : ∀ (u v w x y z : Fin 6),
    let p := [u,v,w,x,y,z]
    p.Nodup → FixedSix.starts.all (fun a => FixedSix.starts.any (works p a))=true := by native_decide

private theorem inside_start (p : C → C) (fixed : ∀ x,6≤x.val → p x=x)
    (low : ∀ x,x.val<6 → (p x).val<6) (inj : Injective p)
    (a : List Nat) (ha : a∈FixedSix.starts) :
    ∃ b ∈ FixedSix.starts, ∀ e∈trial a, Walk (Adj (trial b)) (p e.1) (p e.2) := by
  let vals (k : Fin 6) : Fin 6 := ⟨(p ⟨k.val,by omega⟩).val,low _ k.isLt⟩
  let ls := [vals 0,vals 1,vals 2,vals 3,vals 4,vals 5]
  have vinj : Injective vals := by
    intro i j eq
    apply Fin.ext
    have e : p ⟨i.val,by omega⟩ = p ⟨j.val,by omega⟩ := Fin.ext (congrArg (fun z : Fin 6 => z.val) eq)
    exact congrArg (fun a : C => a.val) (inj e)
  have nd : ls.Nodup := by
    change (([0,1,2,3,4,5] : List (Fin 6)).map vals).Pairwise _
    apply List.pairwise_map.mpr
    exact List.Pairwise.imp (fun h eq => h (vinj eq)) (by decide : ([0,1,2,3,4,5] : List (Fin 6)).Nodup)
  have act (x : C) : rename ls x=p x := by
    by_cases h : x.val<6
    · have split : x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 ∨ x=5 := by
        apply (by decide : ∀ x : C, x.val<6 → x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 ∨ x=5) x h
      rcases split with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
    · simp [rename,h,fixed x (by omega)]
  have all := starts_move (vals 0) (vals 1) (vals 2) (vals 3) (vals 4) (vals 5) nd
  obtain ⟨b,hb,ok⟩ := List.any_eq_true.mp (List.all_eq_true.mp all a ha)
  refine ⟨b,hb,?_⟩
  intro e he
  have hit := List.all_eq_true.mp ok e he
  rw [← act e.1,← act e.2]
  exact walk_of_seen _ _ _ hit

def lift (x : C) : V := ⟨x.val,by omega⟩

private theorem ordinary {f : V→V} {x y : C} : (x,y) ∈ actualEdges f ↔ f (lift x)=lift y := by
  constructor
  · intro mem
    obtain ⟨⟨a,b⟩,row,hit⟩ := List.mem_filterMap.mp mem
    obtain ⟨u,_,eq⟩ := List.mem_map.mp row
    cases eq
    simp only [erase] at hit
    split at hit
    · cases hit; rfl
    · contradiction
  · intro eq
    apply List.mem_filterMap.mpr
    refine ⟨(lift x,lift y),List.mem_map.mpr ⟨lift x,(by decide : ∀ v : V,v∈points) _,Prod.ext rfl eq⟩,?_⟩
    simp [lift,x.isLt,y.isLt]

private theorem reverse {es : E} {x y : C} (h : Walk (Adj es) x y) : Walk (Adj es) y x := by
  induction h with
  | stay => exact .stay _
  | step _ e ih => exact (Walk.step (E:=Adj es) (.stay _) e.symm).join ih

theorem transport (g f : C→V→V) (P : V→V) (p : C→C) (rel : ∀ x, P (lift x)=lift (p x))
    (maps : ∀ c x, f c (P x)=P (g c x)) (fixed : ∀ x,6≤x.val → p x=x)
    (low : ∀ x,x.val<6 → (p x).val<6) (inj : Injective p)
    (surj : Surjective p) (won : Wins g) : Wins f := by
  obtain ⟨groups,mg,_,_,conn⟩ := won
  obtain ⟨a,ma,rest⟩ := List.mem_flatMap.mp mg
  obtain ⟨b,mb,rfl⟩ := List.mem_map.mp rest
  obtain ⟨a',ma',paths⟩ := inside_start p fixed low inj a ma
  have mem : a'++b ∈ FixedSix.all := List.mem_flatMap.mpr ⟨a',ma',List.mem_map.mpr ⟨b,mb,rfl⟩⟩
  have legal : FixedSix.all.all (fun t => decide ((trial t).length=10 ∧ (trial t).Nodup))=true := by native_decide
  obtain ⟨len,nd⟩ := of_decide_eq_true (List.all_eq_true.mp legal _ mem)
  refine ⟨_,mem,len,nd,?_⟩
  intro c v w
  obtain ⟨x,rfl⟩ := surj v
  obtain ⟨y,rfl⟩ := surj w
  let es := trial (a'++b)++actualEdges (f c)
  have send {u v : C} (h : (u,v) ∈ trial (a++b)++actualEdges (g c)) : Walk (Adj es) (p u) (p v) := by
    rcases List.mem_append.mp h with wild|old
    · change (u,v)∈(a++b).flatMap triple at wild
      rw [List.flatMap_append] at wild
      rcases List.mem_append.mp wild with inner|outer
      · apply Walk.mapInto id _ (paths _ inner)
        intro s t go
        apply Walk.step (.stay _)
        have incl (e : Edge 15) (mem : e∈trial a') : e∈es := by
          apply List.mem_append_left
          rw [trial,List.flatMap_append]
          exact List.mem_append_left _ mem
        exact go.imp (incl _) (incl _)
      · have outside : FixedSix.endings.all (fun b => (trial b).all (fun e => 6≤e.1.val && 6≤e.2.val))=true := by native_decide
        have inner := List.all_eq_true.mp (List.all_eq_true.mp outside b mb) _ outer
        have hu : 6≤u.val ∧ 6≤v.val := by simpa using inner
        rw [fixed _ hu.1,fixed _ hu.2]
        exact .step (.stay _) (Or.inl (List.mem_append_left _ (by simpa [trial,List.flatMap_append] using Or.inr (a:=(u,v)∈trial a') outer)))
    · have eq := ordinary.mp old
      have kept : f c (lift (p u))=lift (p v) := by rw [← rel, maps,eq,rel]
      exact .step (.stay _) (Or.inl (List.mem_append_right _ (ordinary.mpr kept)))
  exact Walk.mapInto p (fun _ _ h => h.elim send (fun e => reverse (send e))) (conn c x y)
end InsideNames
