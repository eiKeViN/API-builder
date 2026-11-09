module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
Probe classes have no native composition, pullback, or restriction instances.
Only aggregate mathematical capabilities are transported from their mathlib
counterparts. Therefore successful concrete instance synthesis tests installation.
-/

public section
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AGExperiment

class ProbeFlat {X Y : Scheme} (f : X ⟶ Y) : Prop where
  fact : Flat f
class ProbeEtale {X Y : Scheme} (f : X ⟶ Y) : Prop where
  fact : Etale f
class ProbeSmooth {X Y : Scheme} (f : X ⟶ Y) : Prop where
  fact : Smooth f
class ProbeFinite {X Y : Scheme} (f : X ⟶ Y) : Prop where
  fact : IsFinite f
class ProbeProper {X Y : Scheme} (f : X ⟶ Y) : Prop where
  fact : IsProper f

lemma probeFlat_eq : (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeFlat f) = @Flat := by
  funext X Y f; exact propext ⟨fun h => h.fact, fun h => ⟨h⟩⟩
lemma probeEtale_eq : (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeEtale f) = @Etale := by
  funext X Y f; exact propext ⟨fun h => h.fact, fun h => ⟨h⟩⟩
lemma probeSmooth_eq : (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeSmooth f) = @Smooth := by
  funext X Y f; exact propext ⟨fun h => h.fact, fun h => ⟨h⟩⟩
lemma probeFinite_eq : (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeFinite f) = @IsFinite := by
  funext X Y f; exact propext ⟨fun h => h.fact, fun h => ⟨h⟩⟩
lemma probeProper_eq : (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeProper f) = @IsProper := by
  funext X Y f; exact propext ⟨fun h => h.fact, fun h => ⟨h⟩⟩

instance : MorphismProperty.IsStableUnderComposition (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeFlat f) := by
  rw [probeFlat_eq]; infer_instance
instance : MorphismProperty.IsStableUnderBaseChange (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeFlat f) := by
  rw [probeFlat_eq]; infer_instance
instance : IsZariskiLocalAtTarget (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeFlat f) := by
  rw [probeFlat_eq]; infer_instance
instance : IsZariskiLocalAtSource (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeFlat f) := by
  rw [probeFlat_eq]; infer_instance

instance : MorphismProperty.IsStableUnderComposition (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeEtale f) := by
  rw [probeEtale_eq]; infer_instance
instance : MorphismProperty.IsStableUnderBaseChange (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeEtale f) := by
  rw [probeEtale_eq]; infer_instance
instance : IsZariskiLocalAtTarget (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeEtale f) := by
  rw [probeEtale_eq]; infer_instance
instance : IsZariskiLocalAtSource (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeEtale f) := by
  rw [probeEtale_eq]; infer_instance

instance : MorphismProperty.IsStableUnderComposition (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeSmooth f) := by
  rw [probeSmooth_eq]; infer_instance
instance : MorphismProperty.IsStableUnderBaseChange (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeSmooth f) := by
  rw [probeSmooth_eq]; infer_instance
instance : IsZariskiLocalAtTarget (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeSmooth f) := by
  rw [probeSmooth_eq]; infer_instance
instance : IsZariskiLocalAtSource (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeSmooth f) := by
  rw [probeSmooth_eq]; infer_instance

instance : MorphismProperty.IsStableUnderComposition (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeFinite f) := by
  rw [probeFinite_eq]; infer_instance
instance : MorphismProperty.IsStableUnderBaseChange (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeFinite f) := by
  rw [probeFinite_eq]; infer_instance
instance : IsZariskiLocalAtTarget (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeFinite f) := by
  rw [probeFinite_eq]; infer_instance

instance : MorphismProperty.IsStableUnderComposition (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeProper f) := by
  rw [probeProper_eq]; infer_instance
instance : MorphismProperty.IsStableUnderBaseChange (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeProper f) := by
  rw [probeProper_eq]; infer_instance
instance : IsZariskiLocalAtTarget (fun {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) => ProbeProper f) := by
  rw [probeProper_eq]; infer_instance

end AGExperiment
