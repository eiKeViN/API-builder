module
public meta import ApiRecipes.Command

/-! Fixed semantic iff contracts, including both named directions. -/
public meta section
namespace ApiRecipes.Observation
open Lean Elab Command ApiRecipes.Command

def roles : Array Name := #[`iff_spec, `of_spec, `to_spec]

private partial def sides (type : Term) : CommandElabM (Term × Term) :=
  match type with
  | `($lhs ↔ $rhs) => pure (lhs, rhs)
  | `(($inner)) => sides inner
  | _ => throwError "iff_api: expected an explicit P ↔ Q contract"

syntax (name := iffApi) "iff_api " ("simp ")? ident bracketedBinder* " : " term " := " term : command

@[command_elab iffApi] def elabIffApi : CommandElab := fun s => do
  let useSimp := !s[1].getArgs.isEmpty
  let family ← familyName ⟨s[2]⟩
  let bs : Binders := s[3].getArgs.map (fun b => ⟨b⟩)
  let contract : Term := ⟨s[5]⟩
  let proof : Term := ⟨s[7]⟩
  let (lhs, rhs) ← sides contract
  let publicInputs := bs.map (·.raw) ++ #[contract.raw]
  let hSpec := publicIdent `hSpec publicInputs
  let hPred := publicIdent `hPred publicInputs
  let iffId := mkIdent (`_root_ ++ family ++ `iff_spec)
  batch do
    preflight family roles
    publishTyped (family ++ `iff_spec) bs contract proof useSimp
    publishTyped (family ++ `of_spec) (bs.push (← `(bracketedBinder| ($hSpec : $rhs)))) lhs
      (← `(by
        have hIff : $contract := by apply $iffId <;> assumption
        exact hIff.mpr $hSpec))
    publishTyped (family ++ `to_spec) (bs.push (← `(bracketedBinder| ($hPred : $lhs)))) rhs
      (← `(by
        have hIff : $contract := by apply $iffId <;> assumption
        exact hIff.mp $hPred))
end ApiRecipes.Observation
