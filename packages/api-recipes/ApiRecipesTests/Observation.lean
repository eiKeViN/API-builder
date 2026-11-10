module
public import ApiRecipesTests.ObservationCore
public meta import ApiRecipes.Observation
public section
namespace ApiRecipesTests.Observation

iff_api DoubleAPI (n : ℕ) : Doubled n ↔ ∃ k, n = k + k := doubled_spec n

example (n : ℕ) (h : Doubled n) : ∃ k, n = k + k :=
  DoubleAPI.to_spec (n := n) (hPred := h)
example (n k : ℕ) (h : n = k + k) : Doubled n :=
  DoubleAPI.of_spec (n := n) (hSpec := ⟨k, h⟩)
example (n : ℕ) : Doubled n ↔ ∃ k, n = k + k := DoubleAPI.iff_spec (n := n)

iff_api simp SubsetAPI {α : Type*} (s t : Set α) :
    Included s t ↔ ∀ x, x ∈ s → x ∈ t := included_spec s t

example {α : Type*} (s t : Set α) : Included s t ↔ ∀ x ∈ s, x ∈ t := by
  simp only [SubsetAPI.iff_spec]
example {α : Type*} (s t u : Set α) (hst : Included s t) (htu : Included t u) :
    Included s u := by
  apply SubsetAPI.of_spec
  intro x hx
  exact SubsetAPI.to_spec (s := t) (t := u) (hPred := htu) x
    (SubsetAPI.to_spec (s := s) (t := t) (hPred := hst) x hx)
end ApiRecipesTests.Observation
