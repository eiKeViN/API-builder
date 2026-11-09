module
public import MapBaseline.Recipe

public section

/-! The same six composed client proofs can be reused for generated frontends.
The ModuleAPI pullback client has no RingHomSurjective assumption.
-/

namespace MapBaseline.RecipeClient

open Recipe

section Groups

variable {G H : Type*} [Group G] [Group H] {ι : Sort*}

example (f : G →* H) (p : ι → Subgroup G) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [GroupAPI.map_sup, GroupAPI.map_iSup, GroupAPI.map_bot]

example (f : G →* H) (p : ι → Subgroup H) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [GroupAPI.comap_inf, GroupAPI.comap_iInf, GroupAPI.comap_top]

end Groups

section Rings

variable {R S : Type*} [NonAssocRing R] [NonAssocRing S] {ι : Sort*}

example (f : R →+* S) (p : ι → Subring R) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [RingAPI.map_sup, RingAPI.map_iSup, RingAPI.map_bot]

example (f : R →+* S) (p : ι → Subring S) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [RingAPI.comap_inf, RingAPI.comap_iInf, RingAPI.comap_top]

end Rings

section Modules

variable {R S M N : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
  {σ : R →+* S} {ι : Sort*}

example [RingHomSurjective σ] (f : M →ₛₗ[σ] N) (p : ι → Submodule R M) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [ModuleAPI.map_sup, ModuleAPI.map_iSup, ModuleAPI.map_bot]

/- This is a compile-time check of the strictly weaker comap API. -/
example (f : M →ₛₗ[σ] N) (p : ι → Submodule S N) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [ModuleAPI.comap_inf, ModuleAPI.comap_iInf, ModuleAPI.comap_top]

end Modules

end MapBaseline.RecipeClient
