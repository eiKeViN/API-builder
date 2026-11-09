module
public meta import SmokeProvider.Helper
public meta section
namespace SmokeProvider
public def recipe : ApiBuilder.SmokeRecipe where
  run family := emitValue family (helperValue + 1)
public def wrong : Nat := 0
public def failing : ApiBuilder.SmokeRecipe where
  run _ := Lean.logError "intentional provider generation failure"
end SmokeProvider
