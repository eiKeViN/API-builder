module
public import MapBaseline.Handwritten
public meta import MapBaseline.MacroCommand
public meta import MapBaseline.Contract

namespace MapBaseline.Missing.GroupAPI
variable {G H : Type*} [Group G] [Group H]
derive_map_comap (f : G →* H) using (Subgroup.gc_map_comap f)
  as [map_sup, map_iSup, map_bot, comap_inf, comap_iInf, wrong_top]
end MapBaseline.Missing.GroupAPI

#map_contract MapBaseline.Missing.GroupAPI against MapBaseline.Handwritten.GroupAPI
