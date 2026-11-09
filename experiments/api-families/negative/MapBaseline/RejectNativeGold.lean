module
public import MapBaseline.Handwritten
public meta import MapBaseline.MacroCommand
public meta import MapBaseline.Contract
public section

namespace MapBaseline.GoldLeak.GroupAPI
variable {G H : Type*} [Group G] [Group H]
derive_map_comap (f : G →* H) using (Subgroup.gc_map_comap f)
  as [unused_map_sup, map_iSup, map_bot, comap_inf, comap_iInf, comap_top]
@[simp] theorem map_sup (f : G →* H) (p q : Subgroup G) :
    (p ⊔ q).map f = p.map f ⊔ q.map f := Subgroup.map_sup p q f
end MapBaseline.GoldLeak.GroupAPI

#map_contract MapBaseline.GoldLeak.GroupAPI against MapBaseline.Handwritten.GroupAPI
