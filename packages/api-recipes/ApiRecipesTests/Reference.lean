module
public import ApiRecipesTests.ObservationCore
public import ApiRecipesTests.GeometryCore
public import Mathlib.Analysis.Normed.Operator.Basic
public section
namespace ApiRecipesTests.Reference

namespace DoubleAPI
open ApiRecipesTests.Observation
theorem iff_spec (n : ℕ) : Doubled n ↔ ∃ k, n = k + k := doubled_spec n
theorem of_spec (n : ℕ) (hSpec : ∃ k, n = k + k) : Doubled n := (iff_spec n).mpr hSpec
theorem to_spec (n : ℕ) (hPred : Doubled n) : ∃ k, n = k + k := (iff_spec n).mp hPred
end DoubleAPI

namespace SubsetAPI
open ApiRecipesTests.Observation
theorem iff_spec {α : Type*} (s t : Set α) : Included s t ↔ ∀ x, x ∈ s → x ∈ t := included_spec s t
theorem of_spec {α : Type*} (s t : Set α) (hSpec : ∀ x, x ∈ s → x ∈ t) : Included s t := (iff_spec s t).mpr hSpec
theorem to_spec {α : Type*} (s t : Set α) (hPred : Included s t) : ∀ x, x ∈ s → x ∈ t := (iff_spec s t).mp hPred
end SubsetAPI

namespace AddOnly
variable {F α β : Type*} [FunLike F α β] [Add F] [Add β] [IsAddApply F]
theorem add_apply (f g : F) (x : α) : (f + g) x = f x + g x := IsAddApply.add_apply f g x
theorem coe_add (f g : F) : ⇑(f + g) = ⇑f + ⇑g := FunLike.coe_add f g
end AddOnly

namespace Bounded
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
@[expose] noncomputable def map (L : E →ₗ[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) : E →L[𝕜] F :=
  let _ := hC
  L.mkContinuous C h
theorem map_apply (L : E →ₗ[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) (x : E) : map L C hC h x = L x := rfl
theorem map_zero (L : E →ₗ[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) : map L C hC h 0 = 0 := (map L C hC h).map_zero
theorem map_add (L : E →ₗ[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) (x y : E) :
    map L C hC h (x + y) = map L C hC h x + map L C hC h y := (map L C hC h).map_add x y
theorem map_smul (L : E →ₗ[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) (r : 𝕜) (x : E) :
    map L C hC h (r • x) = r • map L C hC h x := (map L C hC h).map_smul r x
theorem continuous (L : E →ₗ[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) : Continuous (map L C hC h) := (map L C hC h).continuous
theorem norm_le (L : E →ₗ[𝕜] F) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, ‖L x‖ ≤ C * ‖x‖) : ‖map L C hC h‖ ≤ C := L.mkContinuous_norm_le hC h
end Bounded

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ApiRecipesTests.Geometry
set_option backward.isDefEq.respectTransparency.types false
namespace FlatAPI
theorem comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [hf : FlatProbe f] [hg : FlatProbe g] :
    FlatProbe (f ≫ g) := MorphismProperty.comp_mem _ f g hf hg
theorem pullback_fst {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [hg : FlatProbe g] :
    FlatProbe (pullback.fst f g) := MorphismProperty.pullback_fst f g hg
theorem pullback_snd {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [hf : FlatProbe f] :
    FlatProbe (pullback.snd f g) := MorphismProperty.pullback_snd f g hf
theorem restrict {X Y : Scheme} (f : X ⟶ Y) (V : Y.Opens) [hf : FlatProbe f] :
    FlatProbe (f ∣_ V) := IsZariskiLocalAtTarget.restrict hf V
theorem resLE {X Y : Scheme} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (e : U ≤ f ⁻¹ᵁ V) [hf : FlatProbe f] : FlatProbe (f.resLE V U e) :=
  IsZariskiLocalAtSource.resLE (f := f) e hf
end FlatAPI
end ApiRecipesTests.Reference
