module
public import GaloisApiTests.Support
public section
variable {G H : Type*} [Group G] [Group H]

galois_map_api Bad (f : G →* H) using (Subgroup.gc_map_comap f) only [comap_inf]
#assert_absent_galois Bad
