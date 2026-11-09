module
public import Examples.Order.Core
@[expose] public section
namespace OrderExample.Core
def point (X : Obj.{u}) : X.Carrier := X.point
theorem preserves_point {X Y : Obj.{u}} (f : Map X Y) : functionView.view f (point X) = point Y :=
  f.map_point'
end OrderExample.Core
