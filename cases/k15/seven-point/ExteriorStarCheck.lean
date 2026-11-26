import ExteriorStars
namespace ExteriorRows
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem census_checked : hints.size=442975 ∧ starCensus.visited=442975 ∧
    starCensus.rescued=243143 ∧ starCensus.atTen=171870 ∧
    starCensus.atEleven=27944 ∧ starCensus.atTwelve=18 ∧ starCensus.errors=0 := by native_decide
end ExteriorRows
