import RootSystem.An.Construction
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.LinearAlgebra.RootSystem.Irreducible



-- Proof that the root pairing An is reduced
lemma An_is_reduced (n : ℕ) [NeZero n]: (An n).IsReduced := by
  sorry

lemma  An_is_crystallographic (n : ℕ) [NeZero n]: (An n).IsCrystallographic := by
  infer_instance

instance An_is_finite (n : ℕ) [NeZero n] : Fintype (SignedInterval n) := by
  exact Fintype.ofEquiv {x : (Fin n × Fin n) × Bool // x.1.1 ≤ x.1.2}
    { toFun := fun x =>
        { i := x.1.1.1
          j := x.1.1.2
          hij := x.2
          ε := x.1.2 }
      invFun := fun J => ⟨((J.i, J.j), J.ε), J.hij⟩
      left_inv := by
        intro x
        rcases x with ⟨⟨⟨i, j⟩, ε⟩, hij⟩
        rfl
      right_inv := by
        intro J
        cases J
        rfl }

lemma finite (n : ℕ) [NeZero n] : Finite (SignedInterval n) := by
  infer_instance

lemma An__is_irreducible (n : ℕ) [NeZero n] : (An n).IsIrreducible := by
  sorry
