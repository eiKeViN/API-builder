module
public import Mathlib.Algebra.Group.Subgroup.Map
public meta import GaloisApi
public section
namespace ExternalClient
variable {G H : Type*} [Group G] [Group H]
galois_api Exported (f : G →* H) using (Subgroup.gc_map_comap f)
example (f : G →* H) (p q : Subgroup G) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  Exported.map_sup (G := G) (H := H) (f := f) (p := p) (q := q)
example {ι : Sort*} (f : G →* H) (p : ι → Subgroup H) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [Exported.comap_inf, Exported.comap_iInf, Exported.comap_top]
end ExternalClient
