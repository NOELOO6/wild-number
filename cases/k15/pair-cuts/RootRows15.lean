import PairCutCheck15

namespace PairCutCheck15
set_option interpreter.prefer_native true

private theorem row0 : checkRow .oneRoot 0 = true := by native_decide
private theorem row1 : checkRow .oneRoot 1 = true := by native_decide
private theorem row2 : checkRow .oneRoot 2 = true := by native_decide
private theorem row3 : checkRow .oneRoot 3 = true := by native_decide
private theorem row4 : checkRow .oneRoot 4 = true := by native_decide
private theorem row5 : checkRow .oneRoot 5 = true := by native_decide
private theorem row6 : checkRow .oneRoot 6 = true := by native_decide
private theorem row7 : checkRow .oneRoot 7 = true := by native_decide
private theorem row8 : checkRow .oneRoot 8 = true := by native_decide
private theorem row9 : checkRow .oneRoot 9 = true := by native_decide
private theorem row10 : checkRow .oneRoot 10 = true := by native_decide

theorem oneRoot_rows : [checkRow .oneRoot 0, checkRow .oneRoot 1, checkRow .oneRoot 2, checkRow .oneRoot 3, checkRow .oneRoot 4, checkRow .oneRoot 5, checkRow .oneRoot 6, checkRow .oneRoot 7, checkRow .oneRoot 8, checkRow .oneRoot 9, checkRow .oneRoot 10].all id = true := by
  rw [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10]
  decide

end PairCutCheck15
