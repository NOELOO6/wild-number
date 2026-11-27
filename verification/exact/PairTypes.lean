import PairData

namespace WildExact.Seventeen

/-- Count alternating pairs of steps up to the first return. -/
def returnTime (step : V → V) (start x : V) : Nat → Nat
  | 0 => 0
  | k+1 => let next := step x
           if next=start then 1 else 1+returnTime step start next k

def cycleSize (a b : V → V) (x : V) :=
  min (returnTime (b ∘ a) x x 9) (returnTime (a ∘ b) x x 9)

def signature (a b : V → V) :=
  let term := fun x => 1 <<< (5*cycleSize a b x)
  (cycleSize a b root,((List.finRange 18).map term).sum)

def references := (List.finRange 15).map fun i =>
  (signature first (entry (canon i).2),i)

def typeOf (a b : V → V) : Fin 15 :=
  let key := signature a b
  ((references.find? (fun p => p.1==key)).map Prod.snd).getD 0

end WildExact.Seventeen
