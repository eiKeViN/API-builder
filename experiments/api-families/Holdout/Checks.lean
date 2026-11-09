module
public import Holdout.Reference
public import Holdout.Macro
public import Holdout.Recipe
public meta import MapBaseline.Contract

/- Imported rechecks cover signatures and registrations. Proof-dependency audits
run at creation time in Holdout.Macro and the recipe's creation validator. -/
#map_contract Holdout.Macro.SubsemiringAPI against Holdout.Reference.SubsemiringAPI
#map_contract Holdout.Macro.SubalgebraAPI against Holdout.Reference.SubalgebraAPI
#map_contract Holdout.Recipe.SubsemiringAPI against Holdout.Reference.SubsemiringAPI
#map_contract Holdout.Recipe.SubalgebraAPI against Holdout.Reference.SubalgebraAPI
