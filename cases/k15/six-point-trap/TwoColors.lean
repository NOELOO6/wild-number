import LastNineteen
namespace LastNineteen
theorem two_color_bounds : ((List.range 15).all fun c => (List.range c).all fun d =>
    pairBounds FixedSix.rows[c]! FixedSix.rows[d]!)=true := by native_decide
theorem before_and_after :
    SixTrap.visit FixedSix.ordinary 4 32767 [] {} = ⟨120241,1281159,0⟩ ∧
    SixTrap.visit ordinary 4 32767 [] {} = ⟨117194,1284206,0⟩ := by native_decide
#print axioms before_and_after
#print axioms three_color_change
#print axioms every_old_win_now_loses
#print axioms two_color_bounds
end LastNineteen
