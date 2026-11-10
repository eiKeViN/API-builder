module
public import Mathlib.Data.Set.Basic
public section
namespace Evolution
def Doubled (n : ℕ) : Prop := ∃ k : ℕ, n = k + k
lemma observation (n : ℕ) : Doubled n ↔ ∃ k : ℕ, n = k + k := Iff.rfl
end Evolution
