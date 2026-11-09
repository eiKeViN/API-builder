module
public import Examples.Order.Bound
meta import ApiBuilder.FamilyElab
meta import ApiBuilder.Recipes.BundledMap
#api_check OrderExample.Map
open OrderExample
example {X Y : Obj.{u}} (f : Map X Y) : f.comp (Map.id X) = f := by simp
