module
public import GaloisApiTests.Support
public section
variable {G H : Type*} [Group G] [Group H]

galois_api Bad (f : G →* H) using (Subgroup.gc_map_comap f) only [map_supp]
#assert_absent_galois Bad
