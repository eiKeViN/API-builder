module
public import Mathlib.Algebra.Group.IsApply
public meta import ApiRecipes.Command

/-! Native-name export of existing Is*Apply capabilities. -/
public meta section
namespace ApiRecipes.Pointwise
open Lean Elab Command ApiRecipes.Command

def operations : Array Name := #[`zero, `one, `add, `mul, `neg, `inv, `sub, `div]

syntax (name := pointwiseApi) "pointwise_api " ident " for " term selection : command
syntax (name := pointwiseSmulApi) "pointwise_smul_api " ident " for " term " scalars " term : command

@[command_elab pointwiseApi] def elabPointwise : CommandElab := fun s => do
  let family ← familyName ⟨s[1]⟩
  let type : Term := ⟨s[3]⟩
  let selected ← select operations ⟨s[4]⟩
  let roles := selected.flatMap fun op => #[Name.mkSimple (toString op ++ "_apply"),
    Name.mkSimple ("coe_" ++ toString op)]
  batch do
    preflight family roles
    for op in selected do
      let (app, coe) ← match op with
        | `zero => pure (← `(fun (x : _) => IsZeroApply.zero_apply (F := $type) x),
            ← `(FunLike.coe_zero (F := $type)))
        | `one => pure (← `(fun (x : _) => IsOneApply.one_apply (F := $type) x),
            ← `(FunLike.coe_one (F := $type)))
        | `add => pure (← `(fun (f g : $type) (x : _) => IsAddApply.add_apply f g x),
            ← `(fun (f g : $type) => FunLike.coe_add f g))
        | `mul => pure (← `(fun (f g : $type) (x : _) => IsMulApply.mul_apply f g x),
            ← `(fun (f g : $type) => FunLike.coe_mul f g))
        | `neg => pure (← `(fun (f : $type) (x : _) => IsNegApply.neg_apply f x),
            ← `(fun (f : $type) => FunLike.coe_neg f))
        | `inv => pure (← `(fun (f : $type) (x : _) => IsInvApply.inv_apply f x),
            ← `(fun (f : $type) => FunLike.coe_inv f))
        | `sub => pure (← `(fun (f g : $type) (x : _) => IsSubApply.sub_apply f g x),
            ← `(fun (f g : $type) => FunLike.coe_sub f g))
        | `div => pure (← `(fun (f g : $type) (x : _) => IsDivApply.div_apply f g x),
            ← `(fun (f g : $type) => FunLike.coe_div f g))
        | _ => throwError "recipe: internal unsupported pointwise operation"
      publish (family ++ Name.mkSimple (toString op ++ "_apply")) app .simp
      publish (family ++ Name.mkSimple ("coe_" ++ toString op)) coe .coe

@[command_elab pointwiseSmulApi] def elabSmul : CommandElab := fun s => do
  let family ← familyName ⟨s[1]⟩
  let type : Term := ⟨s[3]⟩
  let scalar : Term := ⟨s[5]⟩
  batch do
    preflight family #[`smul_apply, `coe_smul]
    publish (family ++ `smul_apply) (← `(fun (c : $scalar) (f : $type) (x : _) =>
      IsSMulApply.smul_apply f c x)) .simp
    publish (family ++ `coe_smul) (← `(fun (c : $scalar) (f : $type) => FunLike.coe_smul c f)) .coe
end ApiRecipes.Pointwise
