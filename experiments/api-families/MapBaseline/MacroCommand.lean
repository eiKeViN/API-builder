module
public import Mathlib.Order.GaloisConnection.Basic
public meta import Lean.Elab.Command

/-! A dedicated generator baseline. It has no API Builder dependency. -/

public meta section

open Lean Elab Command

namespace MapBaseline.MacroGenerator

private def publicBinderNames : Expr → Expr
  | .forallE name domain body info =>
    .forallE name.eraseMacroScopes domain (publicBinderNames body) info
  | .mdata data body => .mdata data (publicBinderNames body)
  | body => body

elab "map_proof_type% " proof:term : term => do
  let value ← Lean.Elab.Term.elabTerm proof none
  return publicBinderNames (← Lean.Meta.inferType value)

def emitInferred (name : Ident) (proof : Term) : CommandElabM Unit := do
  elabCommand (← `(command|
    @[simp] public theorem $name : map_proof_type% $proof := $proof))

structure Config where
  binders : Array (TSyntax ``Parser.Term.bracketedBinder)
  leftExtra : Array (TSyntax ``Parser.Term.bracketedBinder) := #[]
  source : Term := default
  target : Term := default
  map : Term := default
  comap : Term := default
  gc : Term
  names : Array Ident
  rightProofs : Option (Term × Term × Term) := none

/-- Emit six ordinary simp lemmas. The optional right proofs are checked without
the extra assumptions used only by the left adjoint. Shared by the short command
and any framework adapter, so a comparison need not duplicate generation code. -/
def emit (c : Config) : CommandElabM Unit := do
  unless c.names.size == 6 do throwError "expected six output names"
  let bs := c.binders
  let ls := c.leftExtra
  let fbs := bs.map (fun b => (⟨b.raw⟩ : TSyntax ``Parser.Term.funBinder))
  let fls := ls.map (fun b => (⟨b.raw⟩ : TSyntax ``Parser.Term.funBinder))
  let indexName ← liftCoreM <| mkFreshUserName `uMapComapIndex
  let indexId := mkIdent indexName
  let indexLevel : TSyntax `level := ⟨indexId.raw⟩
  elabCommand (← `(command| universe $indexId))
  let b := c.target
  let u := c.comap
  let gc := c.gc
  let sup := c.names[0]!
  let iSup := c.names[1]!
  let bot := c.names[2]!
  let inf := c.names[3]!
  let iInf := c.names[4]!
  let top := c.names[5]!
  emitInferred sup (← `(term| fun $fls:funBinder* $fbs:funBinder* (p q : _) =>
    GaloisConnection.l_sup (a₁ := p) (a₂ := q) $gc))
  emitInferred iSup (← `(term| fun $fls:funBinder* {ι : Sort $indexLevel} $fbs:funBinder*
    (p : ι → _) => GaloisConnection.l_iSup (f := p) $gc))
  emitInferred bot (← `(term| fun $fls:funBinder* $fbs:funBinder* =>
    GaloisConnection.l_bot $gc))
  match c.rightProofs with
  | none => do
    emitInferred inf (← `(term| fun $fbs:funBinder* (p q : _) =>
      GaloisConnection.u_inf (b₁ := p) (b₂ := q) $gc))
    emitInferred iInf (← `(term| fun {ι : Sort $indexLevel} $fbs:funBinder* (p : ι → _) =>
      GaloisConnection.u_iInf (f := p) $gc))
    emitInferred top (← `(term| fun $fbs:funBinder* => GaloisConnection.u_top $gc))
  | some (infPf, iInfPf, topPf) => do
    emitInferred inf (← `(term| fun $fbs:funBinder* (p q : $b) =>
      ($infPf : $u (p ⊓ q) = $u p ⊓ $u q)))
    emitInferred iInf (← `(term| fun {ι : Sort $indexLevel} $fbs:funBinder*
      (p : ι → $b) => ($iInfPf : $u (⨅ i, p i) = ⨅ i, $u (p i))))
    emitInferred top (← `(term| fun $fbs:funBinder* => ($topPf : $u (⊤ : $b) = ⊤)))

syntax (name := deriveMapComap)
  "derive_map_comap " bracketedBinder* (" left_extra " bracketedBinder*)? " using " term
  " as " "[" ident "," ident "," ident "," ident "," ident "," ident "]"
  (" right_via " "(" term ")" "(" term ")"
    "[" term "," term "," term "]")? : command

elab_rules : command
  | `(derive_map_comap $bs:bracketedBinder* $[left_extra $ls:bracketedBinder*]? using $gc
      as [$sup, $iSup, $bot, $inf, $iInf, $top]
      $[right_via ($b) ($u) [$infPf, $iInfPf, $topPf]]?) => do
    emit {
      binders := bs
      leftExtra := ls.getD #[]
      target := b.getD default, comap := u.getD default, gc := gc
      names := #[sup, iSup, bot, inf, iInf, top]
      rightProofs := do
        let infPf ← infPf
        let iInfPf ← iInfPf
        let topPf ← topPf
        pure (infPf, iInfPf, topPf)
    }

end MapBaseline.MacroGenerator
