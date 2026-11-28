import PairCutCheck15

namespace PairCutCheck15
set_option interpreter.prefer_native true

private theorem row0 : checkRow .clearPairs 0 = true := by native_decide
private theorem row1 : checkRow .clearPairs 1 = true := by native_decide
private theorem row2 : checkRow .clearPairs 2 = true := by native_decide
private theorem row3 : checkRow .clearPairs 3 = true := by native_decide
private theorem row4 : checkRow .clearPairs 4 = true := by native_decide
private theorem row5 : checkRow .clearPairs 5 = true := by native_decide
private theorem row6 : checkRow .clearPairs 6 = true := by native_decide
private theorem row7 : checkRow .clearPairs 7 = true := by native_decide
private theorem row8 : checkRow .clearPairs 8 = true := by native_decide
private theorem row9 : checkRow .clearPairs 9 = true := by native_decide
private theorem row10 : checkRow .clearPairs 10 = true := by native_decide

theorem clearPairs_rows : [checkRow .clearPairs 0, checkRow .clearPairs 1, checkRow .clearPairs 2, checkRow .clearPairs 3, checkRow .clearPairs 4, checkRow .clearPairs 5, checkRow .clearPairs 6, checkRow .clearPairs 7, checkRow .clearPairs 8, checkRow .clearPairs 9, checkRow .clearPairs 10].all id = true := by
  rw [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10]
  decide

end PairCutCheck15
