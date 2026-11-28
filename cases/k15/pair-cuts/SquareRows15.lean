import PairCutCheck15

namespace PairCutCheck15
set_option interpreter.prefer_native true

private theorem row0 : checkRow .squarePairs 0 = true := by native_decide
private theorem row1 : checkRow .squarePairs 1 = true := by native_decide
private theorem row2 : checkRow .squarePairs 2 = true := by native_decide
private theorem row3 : checkRow .squarePairs 3 = true := by native_decide
private theorem row4 : checkRow .squarePairs 4 = true := by native_decide
private theorem row5 : checkRow .squarePairs 5 = true := by native_decide
private theorem row6 : checkRow .squarePairs 6 = true := by native_decide
private theorem row7 : checkRow .squarePairs 7 = true := by native_decide
private theorem row8 : checkRow .squarePairs 8 = true := by native_decide
private theorem row9 : checkRow .squarePairs 9 = true := by native_decide
private theorem row10 : checkRow .squarePairs 10 = true := by native_decide

theorem squarePairs_rows : [checkRow .squarePairs 0, checkRow .squarePairs 1, checkRow .squarePairs 2, checkRow .squarePairs 3, checkRow .squarePairs 4, checkRow .squarePairs 5, checkRow .squarePairs 6, checkRow .squarePairs 7, checkRow .squarePairs 8, checkRow .squarePairs 9, checkRow .squarePairs 10].all id = true := by
  rw [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10]
  decide

end PairCutCheck15
