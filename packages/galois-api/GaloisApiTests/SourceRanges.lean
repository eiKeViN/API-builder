module
public import Mathlib.Algebra.Group.Subgroup.Map
public meta import GaloisApi
public section
namespace GaloisApiTests.SourceRanges
variable {G H : Type*} [Group G] [Group H]
galois_api Exported (f : G →* H) using (Subgroup.gc_map_comap f)
open Lean Elab Command in
run_cmd do
  for role in GaloisApi.allRoles do
    let some ranges ← findDeclarationRanges? (`GaloisApiTests.SourceRanges.Exported ++ role)
      | throwError "missing source range for '{role}'"
    unless ranges.range.pos.line == 7 do
      throwError "source range points away from command invocation: {ranges.range.pos.line}"
end GaloisApiTests.SourceRanges
