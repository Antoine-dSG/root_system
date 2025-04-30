import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.WeylGroup

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (S : Type*) {i j k : ι}

namespace RootPairing

def WeylGeomRepRoots : Prop := 1=1
def WeylGeomRepCoroots : Prop := 1=1


end RootPairing
