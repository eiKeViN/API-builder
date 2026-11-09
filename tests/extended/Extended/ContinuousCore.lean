module
public import Examples.Continuous.Core
@[expose] public section
namespace ContinuousExample.Core
def point (X : Obj.{u}) : X.Carrier := 0
theorem preserves_point {X Y : Obj.{u}} (f : Map X Y) : functionView.view f (point X) = point Y :=
  f.map_zero
end ContinuousExample.Core
