module

public import Mathlib.Algebra.Group.Subgroup.Map

@[expose] public section

/- V2: implementation differs from V1; the public observation is unchanged. -/
namespace Evolution

variable {G H : Type*} [Group G] [Group H]

def map (f : G →* H) (p : Subgroup G) : Subgroup H where
  carrier := Set.range (fun x : p => f x)
  one_mem' := ⟨⟨1, p.one_mem⟩, f.map_one⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x * y, f.map_mul x y⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨x⁻¹, f.map_inv x⟩

@[simp] theorem mem_map {f : G →* H} {p : Subgroup G} {y : H} :
    y ∈ map f p ↔ ∃ x ∈ p, f x = y := by
  constructor
  · rintro ⟨x, hfx⟩
    exact ⟨x, x.property, hfx⟩
  · rintro ⟨x, hx, hfx⟩
    exact ⟨⟨x, hx⟩, hfx⟩

end Evolution

namespace Evolution
variable {G H : Type*} [Group G] [Group H]
theorem gc (f : G →* H) : GaloisConnection (map f) (Subgroup.comap f) := by
  intro p q
  constructor
  · intro h x hx
    exact h (mem_map.mpr ⟨x, hx, rfl⟩)
  · intro h y hy
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hy
    exact h hx
end Evolution
