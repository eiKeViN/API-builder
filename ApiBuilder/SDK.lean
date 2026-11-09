module
public import Lean
public meta section
namespace ApiBuilder
open Lean Elab Command
/-- Milestone-0 execution seam; not the final preparation/receipt SDK. -/
structure Recipe where
  abiVersion : Nat := 0
  run : Name → CommandElabM Unit
end ApiBuilder
