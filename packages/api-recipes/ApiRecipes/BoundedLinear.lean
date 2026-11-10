module
public import Mathlib.Analysis.Normed.Operator.Basic
public meta import ApiRecipes.Command

/-! Build a named continuous linear operator from an explicit norm estimate. -/
public meta section
namespace ApiRecipes.BoundedLinear
open Lean Elab Command ApiRecipes.Command

def roles : Array Name := #[`map, `map_apply, `map_zero, `map_add, `map_smul, `continuous, `norm_le]

syntax (name := boundedLinearApi) "bounded_linear_api " ident bracketedBinder* " using " term
  " where " ppLine (colGt withPosition(field) ppLine)+ : command

@[command_elab boundedLinearApi] def elabBounded : CommandElab := fun s => do
  let family ← familyName ⟨s[1]⟩
  let bs : Binders := s[2].getArgs.map (fun b => ⟨b⟩)
  let args ← explicitArgs bs
  let linear : Term := ⟨s[4]⟩
  let inputs ← fields #[`bound, `nonneg, `estimate] s[6].getArgs
  let bound := inputs[0]!
  let nonneg := inputs[1]!
  let estimate := inputs[2]!
  let mapId := mkIdent (`_root_ ++ family ++ `map)
  let mapCall ← `($mapId $args*)
  let publicInputs := args.map (·.raw) ++ #[linear.raw, bound.raw]
  let x := publicIdent `x publicInputs
  let y := publicIdent `y publicInputs
  let c := publicIdent `r publicInputs
  let xb ← `(bracketedBinder| ($x : _))
  let yb ← `(bracketedBinder| ($y : _))
  batch do
    preflight family roles
    publishDefinition (family ++ `map) bs (← `(LinearMap.mkContinuous $linear $bound $estimate))
    publishTyped (family ++ `map_apply) (bs.push xb) (← `($mapCall $x = $linear $x)) (← `(by rfl)) true
    publishTyped (family ++ `map_zero) bs (← `($mapCall 0 = 0)) (← `(($mapCall).map_zero)) true
    publishTyped (family ++ `map_add) (bs ++ #[xb, yb])
      (← `($mapCall ($x + $y) = $mapCall $x + $mapCall $y)) (← `(($mapCall).map_add $x $y)) true
    let cb ← `(bracketedBinder| ($c : api_recipe_domain% (ContinuousLinearMap.map_smulₛₗ $mapCall)))
    let smul ← `(ContinuousLinearMap.map_smulₛₗ $mapCall $c $x)
    publishTyped (family ++ `map_smul) (bs ++ #[cb, xb]) (← `(api_recipe_type% $smul)) smul true
    publishTyped (family ++ `continuous) bs (← `(Continuous $mapCall)) (← `(($mapCall).continuous))
    publishTyped (family ++ `norm_le) bs (← `(‖$mapCall‖ ≤ $bound))
      (← `(LinearMap.mkContinuous_norm_le $linear $nonneg $estimate))
end ApiRecipes.BoundedLinear
