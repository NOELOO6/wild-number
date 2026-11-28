import PairCutCheck15

namespace PairCutCheck15
set_option interpreter.prefer_native true

private theorem row0 : checkRow .rootFours 0 = true := by native_decide
private theorem row1 : checkRow .rootFours 1 = true := by native_decide
private theorem row2 : checkRow .rootFours 2 = true := by native_decide
private theorem row3 : checkRow .rootFours 3 = true := by native_decide
private theorem row4 : checkRow .rootFours 4 = true := by native_decide
private theorem row5 : checkRow .rootFours 5 = true := by native_decide
private theorem row6 : checkRow .rootFours 6 = true := by native_decide
private theorem row7 : checkRow .rootFours 7 = true := by native_decide
private theorem row8 : checkRow .rootFours 8 = true := by native_decide
private theorem row9 : checkRow .rootFours 9 = true := by native_decide
private theorem row10 : checkRow .rootFours 10 = true := by native_decide

theorem rootFours_rows : [checkRow .rootFours 0, checkRow .rootFours 1, checkRow .rootFours 2, checkRow .rootFours 3, checkRow .rootFours 4, checkRow .rootFours 5, checkRow .rootFours 6, checkRow .rootFours 7, checkRow .rootFours 8, checkRow .rootFours 9, checkRow .rootFours 10].all id = true := by
  rw [row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10]
  decide

end PairCutCheck15
