module
public import Generated
public import Reference
public section
namespace Evolution
example (n : ℕ) : Doubled n ↔ ∃ k, n = k + k := DoubleAPI.iff_spec (n := n)
example (n : ℕ) (h : Doubled n) : ∃ k, n = k + k := DoubleAPI.to_spec (n := n) (hPred := h)
example (n : ℕ) (h : ∃ k, n = k + k) : Doubled n := DoubleAPI.of_spec (n := n) (hSpec := h)
example (n k : ℕ) (h : n = k + k) : Doubled n := DoubleAPI.of_spec n ⟨k, h⟩
end Evolution
