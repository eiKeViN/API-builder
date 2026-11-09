module
public meta import SmokeProvider.Helper
public meta section
namespace SmokeProvider
public def recipe : ApiBuilder.Recipe where
  run family := emitValue family (helperValue + 1)
public def wrong : Nat := 0
public def failing : ApiBuilder.Recipe where
  run _ := Lean.logError "intentional provider generation failure"
end SmokeProvider
