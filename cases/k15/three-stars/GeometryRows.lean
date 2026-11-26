import StarGeometry
namespace ThreeStars
theorem geometric : ∀ k : K, (layouts k).all geometry=true := by native_decide
end ThreeStars
