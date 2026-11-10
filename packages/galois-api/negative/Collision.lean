module
public import GaloisApiTests.Support
public section
variable {G H : Type*} [Group G] [Group H]

@[simp] theorem Bad.map_bot (f : G →* H) : (⊥ : Subgroup G).map f = ⊥ := (Subgroup.gc_map_comap f).l_bot
galois_api Bad (f : G →* H) using (Subgroup.gc_map_comap f)
open Lean Elab Command in
run_cmd do
  for n in #[`map_sup, `map_iSup, `comap_inf, `comap_iInf, `comap_top] do
    if (← getEnv).contains (`Bad ++ n) then throwError "preflight leaked an output"
  unless (← getEnv).contains `Bad.map_bot do throwError "pre-existing output lost"
  logInfo "PREFLIGHT_OK"
