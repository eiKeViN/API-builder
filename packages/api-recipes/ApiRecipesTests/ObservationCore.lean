module
public import Mathlib.Data.Set.Basic
public section
namespace ApiRecipesTests.Observation
def Doubled (n : ℕ) : Prop := ∃ k, n = k + k
def Included {α : Type*} (s t : Set α) : Prop := s ⊆ t
theorem doubled_spec (n : ℕ) : Doubled n ↔ ∃ k, n = k + k := Iff.rfl
theorem included_spec {α : Type*} (s t : Set α) : Included s t ↔ ∀ x, x ∈ s → x ∈ t := Iff.rfl
end ApiRecipesTests.Observation
