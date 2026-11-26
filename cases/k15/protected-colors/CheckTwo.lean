import TwoAnchors
namespace TwoAnchors
set_option interpreter.prefer_native true
set_option maxRecDepth 200000
set_option maxHeartbeats 0

theorem all_free_types : freePrices.toList.map PriceRow.cycles =
    [[4,4,4,4],[4,4,8],[4,6,6],[4,12],[6,10],[8,8],[16]] := by native_decide

private theorem fixedCheck_0 : fixedCheck 0 = true := by native_decide
private theorem fixedCheck_1 : fixedCheck 1 = true := by native_decide
private theorem fixedCheck_2 : fixedCheck 2 = true := by native_decide
private theorem fixedCheck_3 : fixedCheck 3 = true := by native_decide
private theorem fixedCheck_4 : fixedCheck 4 = true := by native_decide
private theorem fixedCheck_5 : fixedCheck 5 = true := by native_decide
private theorem fixedCheck_6 : fixedCheck 6 = true := by native_decide
private theorem fixedCheck_7 : fixedCheck 7 = true := by native_decide
private theorem fixedCheck_8 : fixedCheck 8 = true := by native_decide
private theorem fixedCheck_9 : fixedCheck 9 = true := by native_decide
private theorem fixedCheck_10 : fixedCheck 10 = true := by native_decide

theorem fixedCheck_all : fixedCheck 0 = true ∧
    fixedCheck 1 = true ∧
    fixedCheck 2 = true ∧
    fixedCheck 3 = true ∧
    fixedCheck 4 = true ∧
    fixedCheck 5 = true ∧
    fixedCheck 6 = true ∧
    fixedCheck 7 = true ∧
    fixedCheck 8 = true ∧
    fixedCheck 9 = true ∧
    fixedCheck 10 = true :=
  ⟨fixedCheck_0, fixedCheck_1, fixedCheck_2, fixedCheck_3, fixedCheck_4, fixedCheck_5, fixedCheck_6, fixedCheck_7, fixedCheck_8, fixedCheck_9, fixedCheck_10⟩

private theorem freeCheck_0 : freeCheck 0 = true := by native_decide
private theorem freeCheck_1 : freeCheck 1 = true := by native_decide
private theorem freeCheck_2 : freeCheck 2 = true := by native_decide
private theorem freeCheck_3 : freeCheck 3 = true := by native_decide
private theorem freeCheck_4 : freeCheck 4 = true := by native_decide
private theorem freeCheck_5 : freeCheck 5 = true := by native_decide
private theorem freeCheck_6 : freeCheck 6 = true := by native_decide

theorem freeCheck_all : freeCheck 0 = true ∧
    freeCheck 1 = true ∧
    freeCheck 2 = true ∧
    freeCheck 3 = true ∧
    freeCheck 4 = true ∧
    freeCheck 5 = true ∧
    freeCheck 6 = true :=
  ⟨freeCheck_0, freeCheck_1, freeCheck_2, freeCheck_3, freeCheck_4, freeCheck_5, freeCheck_6⟩

#print axioms fixedCheck_all
#print axioms freeCheck_all
end TwoAnchors
