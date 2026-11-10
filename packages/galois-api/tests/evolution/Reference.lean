module
public import Core
public section
namespace Reference
variable {G H : Type*} [Group G] [Group H]
@[simp] theorem map_sup (f : G →* H) (p q : Subgroup G) :
    Evolution.map f (p ⊔ q) = Evolution.map f p ⊔ Evolution.map f q := (Evolution.gc f).l_sup
@[simp] theorem map_iSup {ι : Sort*} (f : G →* H) (p : ι → Subgroup G) :
    Evolution.map f (⨆ i, p i) = ⨆ i, Evolution.map f (p i) := (Evolution.gc f).l_iSup
@[simp] theorem map_bot (f : G →* H) : Evolution.map f ⊥ = ⊥ := (Evolution.gc f).l_bot
@[simp] theorem comap_inf (f : G →* H) (p q : Subgroup H) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f := (Evolution.gc f).u_inf
@[simp] theorem comap_iInf {ι : Sort*} (f : G →* H) (p : ι → Subgroup H) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f := (Evolution.gc f).u_iInf
@[simp] theorem comap_top (f : G →* H) : (⊤ : Subgroup H).comap f = ⊤ := (Evolution.gc f).u_top
end Reference
