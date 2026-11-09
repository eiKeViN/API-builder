module
public meta import MapBaseline.MacroCommand
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Module.Submodule.Map

public meta import MapBaseline.Contract
public import MapBaseline.Handwritten

public section

namespace MapBaseline.Macro

namespace GroupAPI

variable {G H : Type*} [Group G] [Group H]

derive_map_comap (f : G →* H) using (Subgroup.gc_map_comap f)
  as [map_sup, map_iSup, map_bot, comap_inf, comap_iInf, comap_top]

end GroupAPI

namespace RingAPI

variable {R S : Type*} [NonAssocRing R] [NonAssocRing S]

derive_map_comap (f : R →+* S) using (Subring.gc_map_comap f)
  as [map_sup, map_iSup, map_bot, comap_inf, comap_iInf, comap_top]

end RingAPI

namespace ModuleAPI

variable {R S M N : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
  {σ : R →+* S}

derive_map_comap (f : M →ₛₗ[σ] N) left_extra [RingHomSurjective σ]
  using (Submodule.gc_map_comap f)
  as [map_sup, map_iSup, map_bot, comap_inf, comap_iInf, comap_top]
  right_via (Submodule S N) (Submodule.comap f) [by rfl,
      by ext x; simp only [Submodule.mem_comap, Submodule.mem_iInf], by rfl]

end ModuleAPI

end MapBaseline.Macro

#map_contract MapBaseline.Macro.GroupAPI against MapBaseline.Handwritten.GroupAPI

#map_contract MapBaseline.Macro.RingAPI against MapBaseline.Handwritten.RingAPI

#map_contract MapBaseline.Macro.ModuleAPI against MapBaseline.Handwritten.ModuleAPI
