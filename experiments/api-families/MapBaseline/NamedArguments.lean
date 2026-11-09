module
public import MapBaseline.Macro
public import MapBaseline.Recipe
public section

namespace MapBaseline.NamedArguments
variable {G H : Type*} [Group G] [Group H]

example (f : G →* H) (p q : Subgroup G) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  MapBaseline.Macro.GroupAPI.map_sup (f := f) (p := p) (q := q)

example (f : G →* H) (p q : Subgroup G) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  MapBaseline.Recipe.GroupAPI.map_sup (G := G) (H := H) (f := f) (p := p) (q := q)
end MapBaseline.NamedArguments
