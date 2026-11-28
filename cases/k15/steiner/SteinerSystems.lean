import SteinerSearch
import SteinerSystem

namespace Wild15.Steiner

open WildSteiner


def Genuine (S : System V) (T : Block) := T.a≠T.b ∧ S.third T.a T.b=T.c

private theorem closed_block (S : System V) (T : Block) (h : Genuine S T)
    (x y : V) (xy : x≠y) (hx : member T x=true) (hy : member T y=true) :
    member T (S.third x y)=true := by
  obtain ⟨_,ab⟩ := h
  have ba := (S.swap T.b T.a).trans ab
  have ac : S.third T.a T.c=T.b := ab ▸ S.again T.a T.b
  have bc : S.third T.b T.c=T.a := ab ▸ S.recover T.a T.b
  have ca := (S.swap T.c T.a).trans ac
  have cb := (S.swap T.c T.b).trans bc
  simp only [member,Bool.or_eq_true,beq_iff_eq] at hx hy ⊢
  rcases hx with (rfl|rfl)|rfl <;> rcases hy with (rfl|rfl)|rfl <;> simp_all

private theorem keep_bits : ∀ a b c y : V,
    (32767 ^^^ blockMask ⟨a,b,c⟩).testBit y.val= !member ⟨a,b,c⟩ y := by native_decide

private theorem erase_free (B : Bank) (T : Block) (x y : V) :
    free (eraseBlock B T) x y=(free B x y && !(member T x && member T y)) := by
  have atPoint (f : V → Nat) : (Array.ofFn f)[x.val]! = f x := by
    have h : x.val<(Array.ofFn f).size := by simp
    simp only [getElem!_pos (c:=Array.ofFn f) (i:=x.val) h,Array.getElem_ofFn]
  unfold free
  change ((Array.ofFn (fun u : V => if member T u then row B u &&& (32767 ^^^ blockMask T) else row B u))[x.val]!).testBit y.val=_
  rw [atPoint]
  by_cases h : member T x=true
  · simp [h,Nat.testBit_and,keep_bits T.a T.b T.c y]
  · simp [h]

/-- On a genuine line, its three pairs are available together. -/
def Uniform (S : System V) (B : Bank) := ∀ x y : V,x≠y →
  free B x y=free B x (S.third x y) ∧ free B x y=free B y (S.third x y)

private theorem initial_uniform (S : System V) : Uniform S initial := by
  have all : ∀ x y : V,x≠y → free initial x y=true := by native_decide
  intro x y xy
  rw [all x y xy,all x _ (S.left_ne xy).symm,all y _ (S.right_ne xy).symm]
  exact ⟨rfl,rfl⟩

private theorem uniform_erase (S : System V) (B : Bank) (T : Block) (old : Uniform S B)
    (h : Genuine S T) : Uniform S (eraseBlock B T) := by
  intro x y xy
  let z := S.third x y
  have xyz := closed_block S T h x y xy
  have xzy : member T x=true → member T z=true → member T y=true := by
    simpa only [z,S.again] using closed_block S T h x z (S.left_ne xy).symm
  have yzx : member T y=true → member T z=true → member T x=true := by
    simpa only [z,S.recover] using closed_block S T h y z (S.right_ne xy).symm
  change member T x=true → member T y=true → member T z=true at xyz
  obtain ⟨a,b⟩ := old x y xy
  simp only [erase_free,←a,←b]
  change (_=(_ && !(member T x && member T z))) ∧ (_=(_ && !(member T y && member T z)))
  cases ax : member T x <;> cases ay : member T y <;> cases az : member T z <;> simp_all

private theorem uniform_bank (S : System V) (ts : List Block) (real : ∀ t∈ts,Genuine S t) :
    Uniform S (bankOf ts) := by
  have extend (xs : List Block) (bs : Bank) (ok : Uniform S bs) (rs : ∀ t∈xs,Genuine S t) :
      Uniform S (xs.foldl eraseBlock bs) := by
    induction xs generalizing bs with
    | nil => exact ok
    | cons t tail ih => exact ih _ (uniform_erase S _ t ok (rs _ (by simp))) (fun u hu => rs _ (by simp [hu]))
  exact extend _ _ (initial_uniform S) real

theorem extract (S : System V) (test : List Block → Bool) (depth : Nat) (ts : List Block)
    (real : ∀ t∈ts,Genuine S t) (passed : search test depth (bankOf ts) ts=true) :
    ∃ result,test result=true ∧ ∀ t∈result,Genuine S t := by
  have go (k : Nat) (B : Bank) (xs : List Block) (u : Uniform S B) (h : ∀ t∈xs,Genuine S t)
      (ok : search test k B xs=true) : ∃ result,test result=true ∧ ∀ t∈result,Genuine S t := by
    induction k generalizing B xs with
    | zero => exact ⟨xs,ok,h⟩
    | succ k ih =>
      cases p : pivot B with
      | none => exact ⟨xs,by simpa only [search,p] using ok,h⟩
      | some e =>
        obtain ⟨x,y⟩ := e
        by_cases invalid : x=y ∨ free B x y=false
        · exact ⟨xs,by simpa only [search,p,if_pos invalid] using ok,h⟩
        simp only [not_or] at invalid
        have valid : free B x y=true := by simpa using invalid.2
        have sy := u x y invalid.1
        let t : Block := ⟨x,y,S.third x y⟩
        have good : Genuine S t := ⟨invalid.1,rfl⟩
        simp only [search,p,if_neg (not_or.mpr invalid)] at ok
        have take := List.all_eq_true.mp ok (S.third x y) (List.mem_finRange _)
        have step : search test k (eraseBlock B t) (t::xs)=true := by
          simpa only [←sy.1,←sy.2,valid,Bool.not_true,Bool.false_or] using take
        exact ih _ _ (uniform_erase S _ t u good) (fun s hs => (List.mem_cons.mp hs).elim (fun e => e ▸ good) (h s)) step
  exact go _ _ _ (uniform_bank S ts real) real passed

end Wild15.Steiner
