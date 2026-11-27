import UniversalLower
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Dedup
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring

namespace WildExact.Periodic
open Finset WildDeletion
set_option autoImplicit false
variable {p m k : Nat}

def roundRobin (n : Nat) [NeZero n] : Coloring n n where
  paint x y := x+y
  symm := add_comm
  proper _ _ _ _ _ eq := add_left_cancel eq

abbrev Pattern (k : Nat) := Fin k → Fin 3 → Int
abbrev State (k : Nat) := Fin k × Int

/-- Across one color edge the sheet index is reflected. Store its constant
term for each possible destination triple. -/
def reflections (p : Nat) (a : Pattern k) (s : Int) (i : Fin k) : List (State k) :=
  (List.finRange 3).flatMap fun u => (List.finRange k).flatMap fun j =>
    (List.finRange 3).filterMap fun v =>
      let d := s-a i u-a j v
      if d % (p:Int) = 0 then some (j,d/(p:Int)) else none

def advance (p : Nat) (a : Pattern k) (s : Int) (start : State k) : List (State k) :=
  (reflections p a s start.1).flatMap fun mid =>
    (reflections p a s mid.1).map fun last => (last.1,start.2-mid.2+last.2)

def reached [NeZero k] (p : Nat) (a : Pattern k) (s : Int) : Nat → List (State k)
  | 0 => [(0,0)]
  | r+1 => let xs := reached p a s r; (xs ++ xs.flatMap (advance p a s)).dedup

def point [NeZero (p*m)] (a : Pattern k) (i : Fin k) (z : Int) (v : Fin 3) : Fin (p*m) :=
  ((p: Int)*z+a i v : Int)

private def ordered {n : Nat} (x y : Fin n) := (min x y,max x y)

def lines (p m : Nat) [NeZero (p*m)] (a : Pattern k) : Lines (p*m) :=
  (univ.image (fun h : Fin m × Fin k × Fin 2 =>
    ordered (point (p:=p) (m:=m) a h.2.1 h.1.val 0)
      (point (p:=p) (m:=m) a h.2.1 h.1.val h.2.2.succ))).filter fun e => e.1<e.2

private theorem periodic [NeZero (p*m)] (a : Pattern k) (i : Fin k) (z h : Int) (u : Fin 3) :
    point (p:=p) (m:=m) a i (z+(m:Int)*h) u=point (p:=p) (m:=m) a i z u := by
  have eq : (p:Int)*(z+(m:Int)*h)+a i u=((p:Int)*z+a i u)+(p*m:Nat)*h := by push_cast; ring
  unfold point
  rw [eq,Int.cast_add,Int.cast_mul,Int.cast_natCast,Fin.natCast_self,zero_mul,add_zero]

private theorem arm [NeZero (p*m)] (hm : 0<m) (a : Pattern k)
    (i : Fin k) (z : Int) (c : Fin (p*m)) (v : Fin 3) :
    Walk (Joined (roundRobin (p*m)) (lines p m a) c)
      (point a i z 0) (point a i z v) := by
  let b : Fin m := ⟨(z%(m:Int)).toNat,by have h:=Int.emod_lt_of_pos z (show (0:Int)<m by omega); omega⟩
  have form : (b.val : Int)=z%(m:Int) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have same (u : Fin 3) : point (p:=p) (m:=m) a i z u=point a i b.val u := by
    conv_lhs => rw [←Int.emod_add_ediv z (m:Int),←form]
    exact periodic ..
  rw [same 0,same v]
  let x := point (p:=p) (m:=m) a i b.val 0
  let y := point (p:=p) (m:=m) a i b.val v
  change Walk _ x y
  by_cases eq : x=y
  · rw [eq]; exact .stay _
  have nz : v≠0 := fun h => eq (by simp [x,y,h])
  let t : Fin 2 := ⟨v.val-1,by omega⟩
  have tv : t.succ=v := Fin.ext (show v.val-1+1=v.val by have : v.val≠0 := fun h => nz (Fin.ext h); omega)
  have mem : ordered x y ∈ lines p m a := by
    apply mem_filter.mpr
    constructor
    · apply mem_image.mpr
      exact ⟨(b,i,t),mem_univ _,by simp [x,y,tv]⟩
    · rcases lt_or_gt_of_ne eq with h|h <;> simp [ordered,h,h.le]
  apply Walk.step (.stay _)
  apply Or.inl
  rcases le_total x y with h|h
  · exact Or.inl (by simpa [ordered,h] using mem)
  · exact Or.inr (by simpa [ordered,h] using mem)

private theorem arc_spec {a : Pattern k} {s d : Int} {i j : Fin k}
    (h : (j,d)∈reflections p a s i) :
    ∃ u v, a i u+a j v+(p:Int)*d=s := by
  obtain ⟨u,_,h⟩ := List.mem_flatMap.mp h
  obtain ⟨j',_,h⟩ := List.mem_flatMap.mp h
  obtain ⟨v,_,eq⟩ := List.mem_filterMap.mp h
  dsimp only at eq
  split at eq
  next divisible =>
    cases eq
    refine ⟨u,v,?_⟩
    have h := Int.emod_add_ediv (s-a i u-a j v) (p:Int)
    omega
  next => contradiction

private theorem one_step [NeZero (p*m)] (hm : 0<m) (a : Pattern k) (s q z : Int)
    (c : Fin (p*m)) (hc : (((p:Int)*q+s:Int) : Fin (p*m))=c)
    {i j : Fin k} {d : Int} (h : (j,d)∈reflections p a s i) :
    Walk (Joined (roundRobin (p*m)) (lines p m a) c)
      (point a i z 0) (point a j (q-z+d) 0) := by
  obtain ⟨u,v,eq⟩ := arc_spec h
  let x := point (p:=p) (m:=m) a i z u
  let y := point (p:=p) (m:=m) a j (q-z+d) v
  have link : Walk (Joined (roundRobin (p*m)) (lines p m a) c) x y := by
    by_cases xy : x=y
    · rw [xy]; exact .stay _
    apply Walk.step (.stay _)
    apply Or.inr
    refine ⟨xy,?_⟩
    change (↑((p:Int)*z+a i u) + ↑((p:Int)*(q-z+d)+a j v) : Fin (p*m))=c
    rw [←Int.cast_add,←hc,←eq]
    congr 1
    ring
  exact ((arm hm a i z c u).join link).join (backwards (joined_symm _) (arm hm a j _ c v))

private theorem reached_sound [NeZero k] [NeZero (p*m)] (hm : 0<m) (a : Pattern k)
    (s q : Int) (c : Fin (p*m)) (hc : (((p:Int)*q+s:Int) : Fin (p*m))=c)
    (r : Nat) (t : State k) (h : t∈reached p a s r) (z : Int) :
    Walk (Joined (roundRobin (p*m)) (lines p m a) c) (point a 0 z 0) (point a t.1 (z+t.2) 0) := by
  induction r generalizing t with
  | zero => simp only [reached,List.mem_singleton] at h; subst t; simpa using (Walk.stay (E:=Joined (roundRobin (p*m)) (lines p m a) c) (point a 0 z 0))
  | succ r ih =>
    rcases List.mem_append.mp (List.mem_dedup.mp h) with prev|next
    · exact ih _ prev
    obtain ⟨u,hu,step⟩ := List.mem_flatMap.mp next
    obtain ⟨v,hv,step⟩ := List.mem_flatMap.mp step
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp step
    have first := one_step hm a s q (z+u.2) c hc (i:=u.1) (j:=v.1) (d:=v.2) hv
    have second := one_step hm a s q (q-(z+u.2)+v.2) c hc (i:=v.1) (j:=w.1) (d:=w.2) hw
    simpa only [show q-(q-(z+u.2)+v.2)+w.2=z+(u.2-v.2+w.2) by omega] using ((ih _ hu).join first).join second


/-- A finite list of walks lifts to all sheet counts coprime to the shift.
The conclusion uses the ordinary legal wild edges of the complete graph. -/
theorem pattern_upper [NeZero k] [NeZero (p*m)] (hp : 0<p) (hm : 0<m)
    (a : Pattern k) (step fuel : Nat) (unit : step.Coprime m)
    (covers : ∀ r : Fin p, ∃ i v, a i v % (p:Int)=r.val)
    (routes : ∀ s : Fin p, (0,(step:Int))∈reached p a s.val fuel ∧
      ∀ i : Fin k, ∃ d : Int,(i,d)∈reached p a s.val fuel) :
    Upper (roundRobin (p*m)) (m*(k*2)) := by
  refine ⟨lines p m a,fun _ he => (mem_filter.mp he).2,?_,?_⟩
  · apply (card_le_card (filter_subset ..)).trans
    apply card_image_le.trans
    simp [Fintype.card_prod]
  intro c
  let s : Fin p := ⟨c.val%p,Nat.mod_lt _ hp⟩
  let q : Int := c.val/p
  have color : (((p:Int)*q+s.val:Int):Fin (p*m))=c := by
    have e : (p:Int)*q+s.val=c.val := by simpa [q,s,Int.natCast_mod] using Int.ediv_add_emod (c.val:Int) p
    rw [e,Int.cast_natCast,Fin.cast_val_eq_self]
  let center := fun (i : Fin k) (z : Int) => point (p:=p) (m:=m) a i z 0
  let E := Joined (roundRobin (p*m)) (lines p m a) c
  have hop (z : Int) : Walk E (center 0 z) (center 0 (z+step)) :=
    reached_sound hm a _ q c color fuel _ (routes s).1 z
  have multiple (z : Int) (t : Nat) : Walk E (center 0 z) (center 0 (z+(step:Int)*t)) := by
    induction t with
    | zero => simpa using (Walk.stay (E:=E) (center 0 z))
    | succ n ih => simpa only [Nat.cast_succ,mul_add,mul_one,←add_assoc] using ih.join (hop (z+step*n))
  have signed (t : Int) : Walk E (center 0 0) (center 0 ((step:Int)*t)) := by
    cases t with
    | ofNat n => simpa using multiple 0 n
    | negSucc n =>
      have b := multiple (-(step:Int)*(n+1)) (n+1)
      have eq : -(step:Int)*(n+1)+(step:Int)*((n+1:Nat):Int)=0 := by push_cast; ring
      rw [eq] at b
      rw [show (step:Int)*Int.negSucc n= -(step:Int)*(n+1) by rw [Int.negSucc_eq]; ring]
      exact backwards (joined_symm _) b
  have all (z : Int) : Walk E (center 0 0) (center 0 z) := by
    have bez := Nat.gcd_eq_gcd_ab step m
    rw [show step.gcd m=1 from unit] at bez
    have split : z=(step:Int)*(step.gcdA m*z)+(m:Int)*(step.gcdB m*z) := calc
      z = (1:Int)*z := (one_mul z).symm
      _ = _ := by rw [show (1:Int)=_ from bez]; ring
    conv_rhs => rw [split]
    change Walk E _ (point (p:=p) (m:=m) a 0 (_+_*_) 0)
    rw [periodic]
    exact signed _
  have every (x : Fin (p*m)) : Walk E (center 0 0) x := by
    let r : Fin p := ⟨x.val%p,Nat.mod_lt _ hp⟩
    obtain ⟨i,v,res⟩ := covers r
    let z : Int := (x.val:Int)/p-a i v/p
    have coord : (p:Int)*z+a i v=x.val := by
      have u := Int.emod_add_ediv (x.val:Int) p
      have v' := Int.emod_add_ediv (a i v) p
      change a i v % (p:Int)=(↑(x.val%p):Int) at res
      rw [Int.natCast_mod] at res
      dsimp only [z]; rw [mul_sub]; omega
    have label : point (p:=p) (m:=m) a i z v=x := by
      simp only [point,coord,Int.cast_natCast,Fin.cast_val_eq_self]
    obtain ⟨d,route⟩ := (routes s).2 i
    have move := reached_sound hm a _ q c color fuel _ route (z-d)
    have toCenter : Walk E (center 0 (z-d)) (center i z) := by simpa only [sub_add_cancel] using move
    rw [←label]
    exact ((all _).join toCenter).join (arm hm a i z c v)
  exact fun x y => (backwards (joined_symm _) (every x)).join (every y)

end WildExact.Periodic
