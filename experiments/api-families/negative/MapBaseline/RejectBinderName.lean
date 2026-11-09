module
public import MapBaseline.Handwritten
public meta import MapBaseline.MacroCommand
public meta import MapBaseline.Contract
public section

namespace MapBaseline.Renamed.GroupAPI
variable {G H : Type*} [Group G] [Group H]
derive_map_comap (f : G →* H) using (Subgroup.gc_map_comap f)
  as [unused_map_sup, map_iSup, map_bot, comap_inf, comap_iInf, comap_top]
@[simp] theorem map_sup (f : G →* H) (left right : Subgroup G) :
    (left ⊔ right).map f = left.map f ⊔ right.map f :=
  (Subgroup.gc_map_comap f).l_sup
end MapBaseline.Renamed.GroupAPI

#map_contract MapBaseline.Renamed.GroupAPI against MapBaseline.Handwritten.GroupAPI
