module

public import Evolution.Contract

@[expose] public section

namespace Evolution.Client

variable {G H : Type*} [Group G] [Group H]

theorem image_mem (f : G →* H) (p : Subgroup G) {x : G} (hx : x ∈ p) :
    f x ∈ Evolution.map f p :=
  Evolution.mem_map.mpr ⟨x, hx, rfl⟩

theorem recover_witness (f : G →* H) (p : Subgroup G) {y : H}
    (hy : y ∈ Evolution.map f p) : ∃ x ∈ p, f x = y :=
  Evolution.mem_map.mp hy

theorem mono (f : G →* H) {p q : Subgroup G} (hpq : p ≤ q) :
    Evolution.map f p ≤ Evolution.map f q := by
  intro y hy
  rcases Evolution.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact Evolution.mem_map.mpr ⟨x, hpq hx, rfl⟩

/- Check the chosen simp registration through a downstream use. -/
theorem identity_mem (p : Subgroup G) (x : G) :
    x ∈ Evolution.map (MonoidHom.id G) p ↔ x ∈ p := by
  simp only [Evolution.mem_map, MonoidHom.id_apply, exists_eq_right]

end Evolution.Client
