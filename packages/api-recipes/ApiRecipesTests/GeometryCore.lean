module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public section
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace ApiRecipesTests.Geometry

class FlatProbe {X Y : Scheme} (f : X ⟶ Y) : Prop where
  fact : Flat f
class ProperProbe {X Y : Scheme} (f : X ⟶ Y) : Prop where
  fact : IsProper f
/-- A composite property, distinct from the native individual classes. -/
class FiniteEtaleProbe {X Y : Scheme} (f : X ⟶ Y) : Prop where
  etale : Etale f
  finite : IsFinite f

lemma flat_eq : (fun {X Y : Scheme} (f : X ⟶ Y) => FlatProbe f) = @Flat := by
  funext X Y f; exact propext ⟨fun h => h.fact, fun h => ⟨h⟩⟩
lemma proper_eq : (fun {X Y : Scheme} (f : X ⟶ Y) => ProperProbe f) = @IsProper := by
  funext X Y f; exact propext ⟨fun h => h.fact, fun h => ⟨h⟩⟩
lemma finiteEtale_eq : (fun {X Y : Scheme} (f : X ⟶ Y) => FiniteEtaleProbe f) =
    (fun {X Y : Scheme} (f : X ⟶ Y) => Etale f ∧ IsFinite f) := by
  funext X Y f; exact propext ⟨fun h => ⟨h.etale, h.finite⟩, fun h => ⟨h.1, h.2⟩⟩

instance : MorphismProperty.IsStableUnderComposition
    (fun {X Y : Scheme} (f : X ⟶ Y) => FlatProbe f) := by rw [flat_eq]; infer_instance
instance : MorphismProperty.IsStableUnderBaseChange
    (fun {X Y : Scheme} (f : X ⟶ Y) => FlatProbe f) := by rw [flat_eq]; infer_instance
instance : IsZariskiLocalAtTarget (fun {X Y : Scheme} (f : X ⟶ Y) => FlatProbe f) := by
  rw [flat_eq]; infer_instance
instance : IsZariskiLocalAtSource (fun {X Y : Scheme} (f : X ⟶ Y) => FlatProbe f) := by
  rw [flat_eq]; infer_instance

instance : MorphismProperty.IsStableUnderComposition
    (fun {X Y : Scheme} (f : X ⟶ Y) => ProperProbe f) := by rw [proper_eq]; infer_instance
instance : MorphismProperty.IsStableUnderBaseChange
    (fun {X Y : Scheme} (f : X ⟶ Y) => ProperProbe f) := by rw [proper_eq]; infer_instance
instance : IsZariskiLocalAtTarget (fun {X Y : Scheme} (f : X ⟶ Y) => ProperProbe f) := by
  rw [proper_eq]; infer_instance

instance : MorphismProperty.IsStableUnderComposition
    (fun {X Y : Scheme} (f : X ⟶ Y) => FiniteEtaleProbe f) := by
  rw [finiteEtale_eq]
  change MorphismProperty.IsStableUnderComposition
    ((@Etale : MorphismProperty Scheme) ⊓ (@IsFinite : MorphismProperty Scheme))
  infer_instance
instance : MorphismProperty.IsStableUnderBaseChange
    (fun {X Y : Scheme} (f : X ⟶ Y) => FiniteEtaleProbe f) := by
  rw [finiteEtale_eq]
  change MorphismProperty.IsStableUnderBaseChange
    ((@Etale : MorphismProperty Scheme) ⊓ (@IsFinite : MorphismProperty Scheme))
  infer_instance
instance : IsZariskiLocalAtTarget (fun {X Y : Scheme} (f : X ⟶ Y) => FiniteEtaleProbe f) := by
  rw [finiteEtale_eq]
  change IsZariskiLocalAtTarget
    ((@Etale : MorphismProperty Scheme) ⊓ (@IsFinite : MorphismProperty Scheme))
  infer_instance
end ApiRecipesTests.Geometry
