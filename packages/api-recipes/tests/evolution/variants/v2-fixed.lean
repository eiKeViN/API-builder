module
public import Mathlib.Data.Set.Basic
public section
namespace Evolution
def Doubled (n : ℕ) : Prop := Nonempty {k : ℕ // n = k + k}
lemma observation (n : ℕ) : Doubled n ↔ ∃ k : ℕ, n = k + k := by
  constructor
  · rintro ⟨⟨k, h⟩⟩; exact ⟨k, h⟩
  · rintro ⟨k, h⟩; exact ⟨⟨k, h⟩⟩
end Evolution
