module
public import Extended.Local
meta import ApiBuilder.FamilyElab
meta import Extended.LocalRecipe
#api_check OrderExample.Map
open OrderExample
example {X Y Z : Obj.{u}} (g : Map Y Z) (f : Map X Y) :
    (fun x => g.comp f x) = (fun x => g (f x)) := Map.coe_comp g f
