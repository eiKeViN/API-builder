module
public import GaloisApiTests.Generated
public section

namespace GaloisApiTests.NamedClient

section GroupAPI
variable {G H : Type*} [Group G] [Group H] {ι : Sort*}

example (f : G →* H) (p q : Subgroup G) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  Generated.GroupAPI.map_sup (f := f) (p := p) (q := q)

example (f : G →* H) (p : ι → Subgroup G) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f :=
  Generated.GroupAPI.map_iSup (ι := ι) (f := f) (p := p)

example (f : G →* H) :
    (⊥ : Subgroup G).map f = ⊥ :=
  Generated.GroupAPI.map_bot (f := f)

example (f : G →* H) (p q : Subgroup H) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  Generated.GroupAPI.comap_inf (f := f) (p := p) (q := q)

example (f : G →* H) (p : ι → Subgroup H) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f :=
  Generated.GroupAPI.comap_iInf (ι := ι) (f := f) (p := p)

example (f : G →* H) :
    (⊤ : Subgroup H).comap f = ⊤ :=
  Generated.GroupAPI.comap_top (f := f)

end GroupAPI

section RingAPI
variable {R S : Type*} [NonAssocRing R] [NonAssocRing S] {ι : Sort*}

example (f : R →+* S) (p q : Subring R) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  Generated.RingAPI.map_sup (f := f) (p := p) (q := q)

example (f : R →+* S) (p : ι → Subring R) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f :=
  Generated.RingAPI.map_iSup (ι := ι) (f := f) (p := p)

example (f : R →+* S) :
    (⊥ : Subring R).map f = ⊥ :=
  Generated.RingAPI.map_bot (f := f)

example (f : R →+* S) (p q : Subring S) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  Generated.RingAPI.comap_inf (f := f) (p := p) (q := q)

example (f : R →+* S) (p : ι → Subring S) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f :=
  Generated.RingAPI.comap_iInf (ι := ι) (f := f) (p := p)

example (f : R →+* S) :
    (⊤ : Subring S).comap f = ⊤ :=
  Generated.RingAPI.comap_top (f := f)

end RingAPI

section ModuleAPI
variable {R S M N : Type*} [Semiring R] [Semiring S]
  [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
  {σ : R →+* S} {ι : Sort*}

example [RingHomSurjective σ] (f : M →ₛₗ[σ] N) (p q : Submodule R M) :
    (p ⊔ q).map f = p.map f ⊔ q.map f :=
  Generated.ModuleAPI.map_sup (f := f) (p := p) (q := q)

example [RingHomSurjective σ] (f : M →ₛₗ[σ] N) (p : ι → Submodule R M) :
    (⨆ i, p i).map f = ⨆ i, (p i).map f :=
  Generated.ModuleAPI.map_iSup (ι := ι) (f := f) (p := p)

example [RingHomSurjective σ] (f : M →ₛₗ[σ] N) :
    (⊥ : Submodule R M).map f = ⊥ :=
  Generated.ModuleAPI.map_bot (f := f)

example (f : M →ₛₗ[σ] N) (p q : Submodule S N) :
    (p ⊓ q).comap f = p.comap f ⊓ q.comap f :=
  Generated.ModuleAPI.comap_inf (f := f) (p := p) (q := q)

example (f : M →ₛₗ[σ] N) (p : ι → Submodule S N) :
    (⨅ i, p i).comap f = ⨅ i, (p i).comap f :=
  Generated.ModuleAPI.comap_iInf (ι := ι) (f := f) (p := p)

example (f : M →ₛₗ[σ] N) :
    (⊤ : Submodule S N).comap f = ⊤ :=
  Generated.ModuleAPI.comap_top (f := f)

end ModuleAPI

end GaloisApiTests.NamedClient
