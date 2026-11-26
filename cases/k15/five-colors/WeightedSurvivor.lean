import Teams
namespace FiveColors
set_option maxHeartbeats 0
set_option maxRecDepth 300000

open Teams (total total_cons total_mono transpose)

/-- One blocked candidate contributes its entire weight to the color total. -/
theorem coveredWeight {C : Type} (colors : List C) (blocked : C → Bool) (w : Nat)
    (h : ∃ c ∈ colors, blocked c = true) :
    w ≤ total colors (fun c => if blocked c then w else 0) := by
  induction colors with
  | nil => simp at h
  | cons c cs ih =>
    rw [total_cons]
    by_cases hc : blocked c = true
    · simp [hc]
    · have tail : ∃ d ∈ cs, blocked d = true := by
        obtain ⟨d, hd, hb⟩ := h
        rcases List.mem_cons.mp hd with he | he
        · subst d; exact False.elim (hc hb)
        · exact ⟨d, he, hb⟩
      simpa [hc] using ih tail

/-- Applies to every list of colors satisfying the budgets, even when
    several of them block the same candidate. -/
theorem weighted_survivor {G C : Type} (gs : List G) (cs : List C)
    (w : G → Nat) (blocked : G → C → Bool) (budget : C → Nat)
    (bound : ∀ c ∈ cs, total gs (fun g => if blocked g c then w g else 0) ≤ budget c)
    (room : total cs budget < total gs w) :
    ∃ g ∈ gs, ∀ c ∈ cs, blocked g c = false := by
  apply Classical.byContradiction
  intro no
  have covered (g : G) (hg : g ∈ gs) : ∃ c ∈ cs, blocked g c = true := by
    apply Classical.byContradiction
    intro hn
    apply no
    refine ⟨g, hg, ?_⟩
    intro c hc
    cases he : blocked g c with
    | false => rfl
    | true => exact False.elim (hn ⟨c,hc,he⟩)
  have low := total_mono gs w (fun g => total cs (fun c => if blocked g c then w g else 0))
    (fun g hg => coveredWeight cs (blocked g) (w g) (covered g hg))
  rw [transpose] at low
  have high := total_mono cs (fun c => total gs (fun g => if blocked g c then w g else 0))
    budget bound
  omega

end FiveColors
