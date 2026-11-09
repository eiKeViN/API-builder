module

public import Mathlib.Algebra.Group.Subgroup.Map

@[expose] public section

/- V1: existential in the ambient group, as in Set.image. -/
namespace Evolution

variable {G H : Type*} [Group G] [Group H]

def map (f : G →* H) (p : Subgroup G) : Subgroup H where
  carrier := f '' (p : Set G)
  one_mem' := ⟨1, p.one_mem, f.map_one⟩
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, p.mul_mem hx hy, f.map_mul x y⟩
  inv_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, p.inv_mem hx, f.map_inv x⟩

@[simp] theorem mem_map {f : G →* H} {p : Subgroup G} {y : H} :
    y ∈ map f p ↔ ∃ x ∈ p, f x = y := Iff.rfl

end Evolution
