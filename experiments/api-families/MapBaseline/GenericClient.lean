module
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Module.Submodule.Map

public section

/-! A plain-helper baseline: existing mathlib GaloisConnection lemmas suffice
for these workloads without introducing a new frontend. This has no custom
named API, so its footprint must not be presented as feature-equivalent.
-/

namespace MapBaseline.GenericClient

section Groups

variable {G H : Type*} [Group G] [Group H] {ι : Sort*}

example (f : G →* H) (p : ι → Subgroup G) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [(Subgroup.gc_map_comap f).l_sup,
    (Subgroup.gc_map_comap f).l_iSup, (Subgroup.gc_map_comap f).l_bot]

example (f : G →* H) (p : ι → Subgroup H) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [(Subgroup.gc_map_comap f).u_inf,
    (Subgroup.gc_map_comap f).u_iInf, (Subgroup.gc_map_comap f).u_top]

end Groups

section Rings

variable {R S : Type*} [NonAssocRing R] [NonAssocRing S] {ι : Sort*}

example (f : R →+* S) (p : ι → Subring R) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [(Subring.gc_map_comap f).l_sup,
    (Subring.gc_map_comap f).l_iSup, (Subring.gc_map_comap f).l_bot]

example (f : R →+* S) (p : ι → Subring S) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  rw [(Subring.gc_map_comap f).u_inf,
    (Subring.gc_map_comap f).u_iInf, (Subring.gc_map_comap f).u_top]

end Rings

section Modules

variable {R S M N : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
  {σ : R →+* S} {ι : Sort*}

example [RingHomSurjective σ] (f : M →ₛₗ[σ] N) (p : ι → Submodule R M) :
    ((⨆ i, p i) ⊔ ⊥).map f = (⨆ i, (p i).map f) ⊔ ⊥ := by
  rw [(Submodule.gc_map_comap f).l_sup,
    (Submodule.gc_map_comap f).l_iSup, (Submodule.gc_map_comap f).l_bot]

/- Applying gc.u_inf here would require the unnecessary scalar-surjectivity
hypothesis. Direct preimage laws retain the weaker public theorem type. -/
example (f : M →ₛₗ[σ] N) (p : ι → Submodule S N) :
    ((⨅ i, p i) ⊓ ⊤).comap f = (⨅ i, (p i).comap f) ⊓ ⊤ := by
  ext x
  simp only [Submodule.mem_comap, Submodule.mem_inf, Submodule.mem_iInf,
    Submodule.mem_top, and_true]

end Modules

end MapBaseline.GenericClient
