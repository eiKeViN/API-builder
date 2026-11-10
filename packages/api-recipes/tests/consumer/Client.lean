module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public meta import ApiRecipes
public section
open CategoryTheory AlgebraicGeometry
namespace Consumer

def PairCondition (a b : ℕ) : Prop := a = b ∧ b = a
iff_api PairAPI (a b : ℕ) : PairCondition a b ↔ a = b := by
  unfold PairCondition
  exact ⟨And.left, fun h => ⟨h, h.symm⟩⟩
example (a b : ℕ) (h : a = b) : PairCondition a b := PairAPI.of_spec (a := a) (b := b) (hSpec := h)

bounded_linear_api ZeroAPI using (0 : ℝ →ₗ[ℝ] ℝ) where
  bound := 0
  nonneg := le_refl 0
  estimate := by intro x; simp
pointwise_api OperatorAPI for (ℝ →L[ℝ] ℝ) only [zero, add]
example (L : ℝ →L[ℝ] ℝ) (x : ℝ) : (ZeroAPI.map + L) x = L x := by
  rw [OperatorAPI.add_apply, ZeroAPI.map_apply]
  simp

-- A new class, with no native concrete closure instances.
class SmoothProbe {X Y : Scheme} (f : X ⟶ Y) : Prop where
  fact : Smooth f
lemma smooth_eq : (fun {X Y : Scheme} (f : X ⟶ Y) => SmoothProbe f) = @Smooth := by
  funext X Y f; exact propext ⟨fun h => h.fact, fun h => ⟨h⟩⟩
set_option backward.isDefEq.respectTransparency.types false in
instance : MorphismProperty.IsStableUnderComposition
    (fun {X Y : Scheme} (f : X ⟶ Y) => SmoothProbe f) := by rw [smooth_eq]; infer_instance
scheme_property_api SmoothAPI using SmoothProbe only [comp]
iff_api SmoothAPI {X Y : Scheme} (f : X ⟶ Y) : SmoothProbe f ↔ Smooth f :=
  ⟨fun h => h.fact, fun h => ⟨h⟩⟩
example {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [SmoothProbe f] [SmoothProbe g] :
    SmoothProbe (f ≫ g) := inferInstance
example {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [SmoothProbe f] [SmoothProbe g] :
    Smooth (f ≫ g) := SmoothAPI.to_spec (f := f ≫ g) (hPred := inferInstance)
end Consumer
