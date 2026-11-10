module
public import GaloisApiTests.Support
public section
variable {G H : Type*} [Group G] [Group H]

preimage_api Bad (f : G →* H) using (Subgroup.comap f) on (Subgroup H) where
  inf := by rfl
  iInf := by ext x; simp only [Subgroup.mem_comap, Subgroup.mem_iInf]
  top := by exact True.intro
#assert_absent_galois Bad
preimage_api Bad (f : G →* H) using (Subgroup.comap f) on (Subgroup H) where
  inf := by rfl
  iInf := by ext x; simp only [Subgroup.mem_comap, Subgroup.mem_iInf]
  top := by rfl
#assert_present_comap Bad
