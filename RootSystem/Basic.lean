import Mathlib.LinearAlgebra.RootSystem.Defs
import Mathlib.LinearAlgebra.RootSystem.Reduced


variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (S : Type*) {i j : ι}


namespace RootPairing
lemma name? (hP : IsReduced P) (i j : ι) (h : ¬ LinearIndependent R ![P.coroot i, P.coroot j]) :
    P.coroot i = P.coroot j ∨ P.coroot i = - P.coroot j := sorry

lemma flip_still_reduced (hP : IsReduced P) : IsReduced (P.flip) := by sorry

#print RootPairing.flip_still_reduced

lemma reflection_perm_unique {Q : RootPairing ι R M N} {h1 : Q.toPerfectPairing = P.toPerfectPairing} {h2 : Q.root = P.root} {h3 : Q.coroot = P.coroot} :
    Q.reflection_perm = P.reflection_perm := by
  ext i j
  apply P.root.injective
  nth_rewrite 1 [← h2]
  rw [← Q.reflection_perm_root, ← P.reflection_perm_root, h1, h2, h3]

end RootPairing
