module
public import Reference
public meta import GaloisApi
public section
variable {G H : Type*} [Group G] [Group H]
galois_api Exported (f : G →* H) using (Evolution.gc f)
#check_galois_api Exported against Reference
