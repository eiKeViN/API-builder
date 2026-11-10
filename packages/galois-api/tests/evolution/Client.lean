module
public import Generated
public section
variable {G H : Type*} [Group G] [Group H]
example (f : G →* H) (p q : Subgroup G) :
    Evolution.map f (p ⊔ q) = Evolution.map f p ⊔ Evolution.map f q :=
  Exported.map_sup (f := f) (p := p) (q := q)
example {ι : Sort*} (f : G →* H) (p : ι → Subgroup G) :
    Evolution.map f ((⨆ i, p i) ⊔ ⊥) = (⨆ i, Evolution.map f (p i)) ⊔ ⊥ := by
  rw [Exported.map_sup, Exported.map_iSup, Exported.map_bot]
example (f : G →* H) (p : Subgroup G) (x : G) (hx : x ∈ p) :
    f x ∈ Evolution.map f p := Evolution.mem_map.mpr ⟨x, hx, rfl⟩
example (f : G →* H) (p : Subgroup G) (y : H) (hy : y ∈ Evolution.map f p) :
    ∃ x ∈ p, f x = y := Evolution.mem_map.mp hy
