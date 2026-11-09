module

public import Evolution.Map

@[expose] public section

namespace Evolution.Contract

variable {G H : Type*} [Group G] [Group H]

/- Fixed expected type. This does not prove an arbitrary equivalent statement:
   the candidate declaration itself must have this public interface. -/
theorem checked_mem_map :
    ∀ {f : G →* H} {p : Subgroup G} {y : H},
      y ∈ Evolution.map f p ↔ ∃ x ∈ p, f x = y :=
  @Evolution.mem_map G H _ _

end Evolution.Contract
