import ColorAccounts
namespace WildExact.Seventeen
open WildExact Finset

private theorem ordered2_sum {α : Type} [Fintype α] (f : α → C → C → Int) :
    ordered2 (fun a b => ∑ l,f l a b)=∑ l,ordered2 (f l) := by
  unfold ordered2
  calc
    _ = ∑ a : C, ∑ l, ∑ b∈univ.erase a,f l a b := sum_congr rfl (fun _ _ => sum_comm)
    _ = _ := sum_comm

private theorem ordered3_sum {α : Type} [Fintype α] (f : α → C → C → C → Int) :
    ordered3 (fun a b c => ∑ l,f l a b c)=∑ l,ordered3 (f l) := by
  unfold ordered3
  have swap (a b : C) : (∑ c∈other a b,∑ l,f l a b c)=∑ l,∑ c∈other a b,f l a b c := sum_comm
  simp_rw [swap]
  exact ordered2_sum ..

private theorem adjustment_bound (g : Coloring 17 17) : 3*ordered3 (adjustment g)≤4080 := by
  let h := adjustment g
  have each (a b c : C) : h a b c+h b c a+h c a b≤1 := by
    let i := kind g a b
    let j := kind g a c
    let k := kind g b c
    have sym (x y : C) : kind g x y=kind g y x := type_symmetric ..
    have t := (transfer_budget i j k).2
    change transfer i j k+transfer k (kind g b a) (kind g c a)+transfer (kind g c a) (kind g c b) i ≤ 1
    rw [sym b a,sym c a,sym c b]
    change transfer i j k+transfer k i j+transfer j k i≤1
    rw [(transfer_budget j k i).1]
    omega
  have bound : ordered3 (fun a b c => h a b c+h b c a+h c a b)≤ ordered3 (fun _ _ _ => 1) := by
    unfold ordered3 ordered2
    exact sum_le_sum (fun a _ => sum_le_sum (fun b _ => sum_le_sum (fun c _ => each a b c)))
  have n : ordered3 (fun _ _ _ => 1)=4080 := by decide
  have sum3 (p q : C → C → C → Int) : ordered3 (fun a b c => p a b c+q a b c)=ordered3 p+ordered3 q := by
    simp only [ordered3,ordered2,sum_add_distrib]
  rw [sum3,sum3,n] at bound
  have once := cycle3 h
  have twice := cycle3 (fun a b c => h b c a)
  change ordered3 (fun a b c => h b c a)=ordered3 (fun a b c => h c a b) at twice
  change 3*ordered3 h≤4080
  omega

private theorem triple_budget (g : Coloring 17 17) :
    ordered3 (fun a b c => (tripleScore (partners g a) (partners g b) (partners g c):Int)) ≤
    5*ordered2 (fun a b => (pairScore (partners g a) (partners g b):Int))-136*3973540+680 := by
  let p := fun a b => (pairScore (partners g a) (partners g b):Int)
  let t := fun a b c => (tripleScore (partners g a) (partners g b) (partners g c):Int)
  let h := adjustment g
  have each (a b : C) (hb : b∈univ.erase a) :
      4*(∑ c∈other a b,t a b c)≤20*p a b-2*3973540+2*∑ c∈other a b,h a b c :=
    (accounts g a b (mem_erase.mp hb).1.symm).2
  have total : ordered2 (fun a b => 4*∑ c∈other a b,t a b c) ≤
      ordered2 (fun a b => 20*p a b-2*3973540+2*∑ c∈other a b,h a b c) :=
    sum_le_sum (fun a _ => sum_le_sum (each a))
  have flat : 4*ordered3 t≤20*ordered2 p-ordered2 (fun _ _ => 2*3973540)+2*ordered3 h := by
    simpa only [ordered2,ordered3,sum_add_distrib,sum_sub_distrib,←mul_sum] using total
  have n : ordered2 (fun _ _ => 2*3973540)=272*(2*3973540) := by decide
  rw [n] at flat
  have cap : 3*ordered3 h≤4080 := adjustment_bound g
  change ordered3 t≤5*ordered2 p-136*3973540+680
  omega

def failing (f : C → V → V) (l : Layout) := univ.filter (fun c => lost (f c) l)
def wins (f : C → V → V) : Int := ∑ l : Layout,if (failing f l).card=0 then 1 else 0

/-- Every admissible coloring has at least 403,637 layouts on which all colors pass the cut test. -/
theorem many_wins (g : Coloring 17 17) : 403637≤wins (partners g) := by
  let f := partners g
  let s := failing f
  let p := fun a b => (pairScore (f a) (f b):Int)
  let t := fun a b c => (tripleScore (f a) (f b) (f c):Int)
  have hit (l : Layout) (c : C) : c∈s l ↔ lost (f c) l=true := by simp [s,failing]
  have s1 (a : C) : (singleScore (f a):Int)=∑ l,if a∈s l then 1 else 0 := by
    simp only [singleScore,score_univ,Nat.cast_sum,hit]
    apply sum_congr rfl; intro l _; split <;> rfl
  have p2 (a b : C) : p a b=∑ l,if a∈s l ∧ b∈s l then 1 else 0 := by
    simp only [p,pairScore,score_univ,Nat.cast_sum,shared,Bool.and_eq_true,hit]
    apply sum_congr rfl; intro l _; split <;> rfl
  have t3 (a b c : C) : t a b c=∑ l,if a∈s l ∧ b∈s l ∧ c∈s l then 1 else 0 := by
    simp only [t,tripleScore,score_univ,Nat.cast_sum,shared,Bool.and_eq_true,hit,and_assoc]
    apply sum_congr rfl; intro l _; split <;> rfl
  have singles (a : C) : singleScore (f a)=8230880 := by
    by_cases eq : a=0
    · exact (accounts g a 1 (by rw [eq]; decide)).1
    · exact (accounts g a 0 eq).1
  have first : (∑ l,(s l).card : Int)=17*8230880 := by
    simp_rw [←one_moment,sum_comm (s:= (univ : Finset Layout)) (t:= (univ : Finset C)),←s1,singles]
    decide
  have second : ordered2 p=∑ l,(((s l).card*((s l).card-1):Nat):Int) := by
    simp only [funext₂ p2,ordered2_sum,two_moment]
  have third : ordered3 t=∑ l,(((s l).card*((s l).card-1)*((s l).card-2):Nat):Int) := by
    have eq := funext (fun a => funext (fun b => funext (t3 a b)))
    simp only [eq,ordered3_sum,three_moment]
  have budget : ordered3 t≤5*ordered2 p-136*3973540+680 := triple_budget g
  have cubic := sum_le_sum (s:= (univ : Finset Layout)) (fun l _ => moment_scalar (s l))
  have mass : (∑ _ : Layout,(1:Int))=95295200 := by simp [Fintype.card_prod]
  simp only [sum_sub_distrib,sum_add_distrib,←mul_sum,mul_sub] at cubic
  change 403637≤∑ l : Layout,if (s l).card=0 then (1:Int) else 0
  omega

end WildExact.Seventeen
