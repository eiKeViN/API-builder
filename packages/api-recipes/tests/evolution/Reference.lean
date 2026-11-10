module
public import Core
public section
namespace Evolution.Reference
lemma iff_spec (n : ℕ) : Doubled n ↔ ∃ k, n = k + k := observation n
lemma of_spec (n : ℕ) (hSpec : ∃ k, n = k + k) : Doubled n := (iff_spec n).mpr hSpec
lemma to_spec (n : ℕ) (hPred : Doubled n) : ∃ k, n = k + k := (iff_spec n).mp hPred
end Evolution.Reference
