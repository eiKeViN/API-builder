module
public meta import ApiBuilder.Recipes.BundledMap
public meta section
namespace BadRecipes
open Lean Elab Command ApiBuilder ApiBuilder.Recipes

def preparation : Recipe where
  prepare r := do
    logError "intentional preparation error"
    prepareBundledMap r

def loggedValidator : Validator where
  check _ := logError "intentional validator error"

def validator : Recipe where
  prepare r := do
    let p ← prepareBundledMap r
    pure { p with validators := p.validators.push ``loggedValidator }

def duplicate : Recipe where
  prepare r := do
    let p ← prepareBundledMap r
    pure { p with outputs := p.outputs.push { p.outputs[0]! with owner := `otherStage } }

def lateProof : Recipe where
  prepare r := do
    let p ← prepareBundledMap r
    pure { p with execute := do
      p.execute
      declare r (← `(example : False := by exact True.intro)) }

def sorryProof : Recipe where
  prepare r := do
    let p ← prepareBundledMap r
    let name := r.family ++ `bad
    pure { p with
      outputs := p.outputs.push { role := `bad, name, owner := `bad }
      execute := do
        p.execute
        let id := mkIdent name
        declare r (← `(public theorem $id : False := by sorry)) }

def wrong : Nat := 0
universe u
def polymorphic : Recipe := { prepare := fun r => do
  let _ : Type u := PUnit
  prepareBundledMap r }
end BadRecipes
