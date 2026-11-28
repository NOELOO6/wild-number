import CutPrices30

namespace WildSieve.Thirty

def probability (k : Nat) : ℚ := prescribe 30 k

def longMass : ℚ := (29 * Nat.choose 15 6 * triples 4 * triples 6 : Nat) / (triples 10 : ℚ)

def lossCap : ℚ := 605121482350997 / 606230625000000

private theorem trim {α : Type} (l : List α) (v f : α → ℚ) :
    (l.map fun j => f j*v j).sum =
      ((l.filter (fun j => decide (f j ≠ 0))).map fun j => f j*v j).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : f a=0 <;> simp [ha,ih]

theorem total_objective (amount : Column → ℚ) :
    total amount objective = amount (.hist 0 0 0) - amount .defect/18000 := by
  have enum : columns.filter (fun j => decide (objective j≠0))=[.hist 0 0 0,.defect] := by
    native_decide
  rw [total,trim,enum]
  simp [objective]
  ring

/-- Combining the first three graph moments and the long-cut bound is affine in
the multiplicity defect. Its slope is negative at every nonnegative defect. -/
theorem loss_budget (d x y m i p s short long : ℚ) (hd : 0≤d)
    (hx : 50*probability 4*((13195-d)*3004-3116*d) ≤ x)
    (hy : probability 3/2*(4060*1898-2640*d) ≤ y)
    (hm : m ≤ x*(9420*probability 6/(3*probability 4)))
    (hi : i ≤ y*(14800*probability 5/probability 3))
    (hp : p ≤ y*(51*probability 4/probability 3))
    (hs : s ≤ y*(51*probability 4/(3*probability 3)))
    (hshort : short ≤ (13195-d)*10*probability 2 - 5/6*x - 2/3*y + m/2+i/2+p/3+s/2)
    (hlong : long ≤ longMass*(longPrice+d/18000)) :
    short+long ≤ lossCap := by
  norm_num [probability,prescribe,triples,Nat.factorial,longMass,longPrice,lossCap,
    Nat.choose_eq_fast_choose,Nat.fast_choose] at *
  linarith only [hx,hy,hm,hi,hp,hs,hshort,hlong,hd]

/-- An integer count of surviving partitions obeys the stronger rounded bound. -/
theorem winners_of_loss (bad good : Nat) (complete : good+bad=triples 10)
    (loss : (bad : ℚ)/(triples 10 : ℚ) ≤ lossCap) : 2211739995828567 ≤ good := by
  norm_num [triples,Nat.factorial,lossCap] at complete loss
  have cap : bad ≤ 1206672005673771433 := by
    by_contra! h
    have high : (1206672005673771434 : ℚ) ≤ (bad : ℚ) := by exact_mod_cast h
    linarith
  omega

#print axioms loss_budget
#print axioms winners_of_loss

end WildSieve.Thirty
