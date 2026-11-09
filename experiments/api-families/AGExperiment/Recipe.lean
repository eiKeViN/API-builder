module
public meta import ApiBuilder.Family
public meta import AGExperiment.Install

public meta section
namespace AGExperiment
open Lean Elab Command ApiBuilder

/-- The same generator as the standalone baseline, with framework-owned receipts
and effect/axiom audits. Aggregate mathematical capabilities remain mathlib inputs. -/
def schemeProperty : ApiBuilder.Recipe where
  prepare request := do
    let propertySyntax ← request.field `property
    let propertyName ← resolvePublic propertySyntax
    unless request.family == propertyName do
      throwError "this bounded recipe requires family name to equal its concrete property class"
    let source? := request.fields.find? (·.key == `source_restriction)
    let mut inputs := #[(`property, propertyName)]
    let mut consumed := #[`property]
    if let some source := source? then
      let sourceName ← resolvePublic source.value
      unless sourceName == `AGExperiment.sourceRestriction do
        throwErrorAt source.ref "expected AGExperiment.sourceRestriction marker"
      inputs := inputs.push (`source_restriction, sourceName)
      consumed := consumed.push `source_restriction
    let roles := if source?.isSome then
      #[(`comp, `api_comp), (`fst, `api_fst), (`snd, `api_snd),
        (`restrict, `api_restrict), (`sourceContract, `api_sourceContract), (`resLE, `api_resLE)]
      else #[(`comp, `api_comp), (`fst, `api_fst), (`snd, `api_snd), (`restrict, `api_restrict)]
    let outputs := roles.map fun (role, suffix) =>
      { role, name := propertyName ++ suffix, owner := `AGExperiment.schemeProperty,
        registrations := if role == `sourceContract then #[] else #[`instance] : Output }
    return {
      consumed, inputs, outputs, validators := #[]
      execute := do
        installCore ⟨propertySyntax⟩
        if source?.isSome then installSource ⟨propertySyntax⟩
    }

end AGExperiment
