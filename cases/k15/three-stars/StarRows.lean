import ThreeStars
namespace ThreeStars
theorem vvv : verify 0 = true := by native_decide
theorem vv0 : verify 1 = true := by native_decide
theorem v00 : verify 2 = true := by native_decide
theorem v01 : verify 3 = true := by native_decide
theorem c000 : verify 4 = true := by native_decide
theorem c001 : verify 5 = true := by native_decide
theorem c012 : verify 6 = true := by native_decide
theorem checked (k : K) : verify k = true := by
  have all : ∀ j : K, j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5 ∨ j=6 := by decide
  rcases all k with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact vvv
  · exact vv0
  · exact v00
  · exact v01
  · exact c000
  · exact c001
  · exact c012
/-- Published counts and rounded-up percentages, in hundredths of a percent. -/
theorem table : ∀ k : K, (layouts k).length = #[6912,5888,4864,3840,6912,2688,3840][k.val]! ∧
    (Teams.total VertexRedraw.colors (fun c => (costs k)[c.val]!) + Teams.total entries (fee k))*10000 ≤
    #[8872,9006,9318,9284,9793,9679,9624][k.val]! * Teams.total (layouts k) Layout.weight := by native_decide
#print axioms checked
end ThreeStars
