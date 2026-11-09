module
public import MapBaseline.Macro
public section

namespace MapBaseline.MacroNamedArguments

section GroupAPI
variable {G H : Type*} [Group G] [Group H] {ι : Sort*}

example (f : G →* H) (p q : Subgroup G) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  Macro.GroupAPI.map_sup (f := f) (p := p) (q := q)

example (f : G →* H) (p : ι → Subgroup G) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f :=
  Macro.GroupAPI.map_iSup (ι := ι) (f := f) (p := p)

example (f : G →* H) :
    (⊥ : Subgroup G).map f = ⊥ :=
  Macro.GroupAPI.map_bot (f := f)

example (f : G →* H) (p q : Subgroup H) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  Macro.GroupAPI.comap_inf (f := f) (p := p) (q := q)

example (f : G →* H) (p : ι → Subgroup H) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f :=
  Macro.GroupAPI.comap_iInf (ι := ι) (f := f) (p := p)

example (f : G →* H) :
    (⊤ : Subgroup H).comap f = ⊤ :=
  Macro.GroupAPI.comap_top (f := f)

end GroupAPI

section RingAPI
variable {R S : Type*} [NonAssocRing R] [NonAssocRing S] {ι : Sort*}

example (f : R →+* S) (p q : Subring R) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  Macro.RingAPI.map_sup (f := f) (p := p) (q := q)

example (f : R →+* S) (p : ι → Subring R) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f :=
  Macro.RingAPI.map_iSup (ι := ι) (f := f) (p := p)

example (f : R →+* S) :
    (⊥ : Subring R).map f = ⊥ :=
  Macro.RingAPI.map_bot (f := f)

example (f : R →+* S) (p q : Subring S) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  Macro.RingAPI.comap_inf (f := f) (p := p) (q := q)

example (f : R →+* S) (p : ι → Subring S) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f :=
  Macro.RingAPI.comap_iInf (ι := ι) (f := f) (p := p)

example (f : R →+* S) :
    (⊤ : Subring S).comap f = ⊤ :=
  Macro.RingAPI.comap_top (f := f)

end RingAPI

section ModuleAPI
variable {R S M N : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
  {σ : R →+* S} {ι : Sort*}

example [RingHomSurjective σ] (f : M →ₛₗ[σ] N) (p q : Submodule R M) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  Macro.ModuleAPI.map_sup (f := f) (p := p) (q := q)

example [RingHomSurjective σ] (f : M →ₛₗ[σ] N) (p : ι → Submodule R M) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f :=
  Macro.ModuleAPI.map_iSup (ι := ι) (f := f) (p := p)

example [RingHomSurjective σ] (f : M →ₛₗ[σ] N) :
    (⊥ : Submodule R M).map f = ⊥ :=
  Macro.ModuleAPI.map_bot (f := f)

example (f : M →ₛₗ[σ] N) (p q : Submodule S N) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  Macro.ModuleAPI.comap_inf (f := f) (p := p) (q := q)

example (f : M →ₛₗ[σ] N) (p : ι → Submodule S N) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f :=
  Macro.ModuleAPI.comap_iInf (ι := ι) (f := f) (p := p)

example (f : M →ₛₗ[σ] N) :
    (⊤ : Submodule S N).comap f = ⊤ :=
  Macro.ModuleAPI.comap_top (f := f)

end ModuleAPI

end MapBaseline.MacroNamedArguments
