module
public import GaloisApiTests.Support
public section
variable {G H : Type*} [Group G] [Group H]

galois_api Bad (f : G →* H) using True.intro
#assert_absent_galois Bad
