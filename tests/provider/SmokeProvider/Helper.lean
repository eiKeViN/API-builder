module
public meta import ApiBuilder.SDK
public meta section
namespace SmokeProvider
open Lean Elab Command
public def helperValue : Nat := 20
public def emitValue (family : Name) (value : Nat) : CommandElabM Unit := do
  let output := mkIdent (family ++ `value)
  let valueSyntax := Syntax.mkNumLit (toString value)
  elabCommand (← `(@[expose] public def $output : Nat := $valueSyntax))
end SmokeProvider
