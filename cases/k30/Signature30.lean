import CutModel30

namespace WildSieve.Thirty

/-- The four rows have the degrees of two triples and the remaining sides. -/
structure Fits (t : Nat) (s : Signature) : Prop where
  first : 2*s.a+s.b+s.c+s.d=3
  second : s.b+2*s.f+s.g+s.h=3
  left : s.c+s.g+2*s.x+s.y=leftFree t
  right : s.d+s.h+s.y+2*s.z=24-leftFree t

theorem mem_signatures {t : Nat} {s : Signature} (ok : Fits t s) : s∈signatures t := by
  obtain ⟨ha,hb,hl,hr⟩ := ok
  unfold signatures
  simp only [List.bind_eq_flatMap,List.mem_flatMap,List.mem_range]
  refine ⟨s.a,by omega,s.b,by omega,s.c,by omega,s.f,by omega,s.g,by omega,?_⟩
  have d : 3-2*s.a-s.b-s.c=s.d := by omega
  have h : 3-s.b-2*s.f-s.g=s.h := by omega
  rw [d,h]
  have first : s.c+s.g≤leftFree t ∧ s.d+s.h≤24-leftFree t := by omega
  simp [guard,first,List.bind_eq_flatMap,List.mem_flatMap]
  refine ⟨s.x,by omega,?_⟩
  have y : leftFree t-s.c-s.g-2*s.x=s.y := by omega
  have z : (24-leftFree t-s.d-s.h-s.y)/2=s.z := by omega
  rw [y]
  have last : s.y≤24-leftFree t-s.d-s.h ∧ (24-leftFree t-s.d-s.h-s.y)%2=0 := by omega
  simp [last,z,show leftFree t ≤ 24-leftFree t-s.d-s.h+2*s.x+s.g+s.c by omega]

end WildSieve.Thirty
