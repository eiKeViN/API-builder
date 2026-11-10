module
public import Core
public meta import ApiRecipes.Observation
public section
namespace Evolution
iff_api DoubleAPI (n : ℕ) : Doubled n ↔ ∃ k, n = k + k := observation n
end Evolution
