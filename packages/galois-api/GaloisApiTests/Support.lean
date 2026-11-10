module
public import Mathlib.Algebra.Group.Subgroup.Map
public meta import GaloisApi
public meta section
open Lean Elab Command

syntax (name := assertAbsentGalois) "#assert_absent_galois " ident : command
@[command_elab assertAbsentGalois] def assertAbsent : CommandElab := fun s => do
  for role in GaloisApi.allRoles do
    if (← getEnv).contains (s[1].getId ++ role) then
      throwError "unexpected surviving output '{role}'"
  logInfo "ROLLBACK_OK"

syntax (name := assertPresentGalois) "#assert_present_comap " ident : command
@[command_elab assertPresentGalois] def assertPresent : CommandElab := fun s => do
  for role in GaloisApi.comapRoles do
    unless ((← getEnv).setExporting true).contains (s[1].getId ++ role) do
      throwError "missing recovered output '{role}'"
  logInfo "RECOVERY_OK"
