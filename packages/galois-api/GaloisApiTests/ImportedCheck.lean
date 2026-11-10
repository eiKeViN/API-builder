module
public import GaloisApiTests.Generated
public meta import GaloisApi

#check_galois_api GaloisApiTests.Generated.GroupAPI against GaloisApiTests.Reference.GroupAPI
#check_galois_api GaloisApiTests.Generated.RingAPI against GaloisApiTests.Reference.RingAPI
#check_galois_api GaloisApiTests.Generated.ModuleAPI against GaloisApiTests.Reference.ModuleAPI
#check_galois_api GaloisApiTests.Generated.SubsemiringAPI against GaloisApiTests.Reference.SubsemiringAPI
#check_galois_api GaloisApiTests.Generated.SubalgebraAPI against GaloisApiTests.Reference.SubalgebraAPI

open Lean Elab Command in
run_cmd do
  if (← getEnv).contains `ApiBuilder.Recipe then
    throwError "standalone consumer unexpectedly imported the recipe framework"
