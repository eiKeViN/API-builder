module
public import GaloisApiTests.Support
public section
variable {G H : Type*} [Group G] [Group H]

preimage_api Bad (f : G →* H) using (Subgroup.comap f) on (Subgroup H) where
  typo := by rfl
#assert_absent_galois Bad
