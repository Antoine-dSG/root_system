import RootSystem.An.Construction
import Mathlib.LinearAlgebra.RootSystem.Reduced
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.LinearAlgebra.RootSystem.Irreducible



instance finite (n : ℕ) [NeZero n] : Fintype (SignedInterval n) := by
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

lemma An_is_finite (n : ℕ) [NeZero n] : Finite (SignedInterval n) := by
  infer_instance

-- Proof that the root pairing An is reduced
lemma An_is_reduced (n : ℕ) [NeZero n] : (An n).IsReduced := by
  rw [RootPairing.isReduced_iff]
  intro J K hlin
  have hcw : (An n).coxeterWeight J K = 4 := by
    exact (RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent (An n)).2 hlin
  change ((Zn_pairing n (α J)) (α_dual K) * (Zn_pairing n (α K)) (α_dual J) = 4) at hcw
  rw [pairing_formula K J, pairing_formula J K] at hcw
  obtain ⟨Ji, Jj, Jh, Jε⟩ := J
  obtain ⟨Ki, Kj, Kh, Kε⟩ := K
  cases Jε <;> cases Kε
  · simp +decide only [SignedInterval.sign] at hcw
    have hends : Ji = Ki ∧ Jj = Kj := by
      split_ifs at hcw <;> constructor <;> apply Fin.ext <;> omega
    rcases hends with ⟨hi, hj⟩
    subst Ki
    subst Kj
    left
    rfl
  · simp +decide only [SignedInterval.sign] at hcw
    have hends : Ji = Ki ∧ Jj = Kj := by
      split_ifs at hcw <;> constructor <;> apply Fin.ext <;> omega
    rcases hends with ⟨hi, hj⟩
    subst Ki
    subst Kj
    right
    ext t
    change α ({ i := Ji, j := Jj, hij := Jh, ε := false } : SignedInterval n) t =
      - α ({ i := Ji, j := Jj, hij := Kh, ε := true } : SignedInterval n) t
    rw [α_eval, α_eval]
    simp [SignedInterval.sign]
  · simp +decide only [SignedInterval.sign] at hcw
    have hends : Ji = Ki ∧ Jj = Kj := by
      split_ifs at hcw <;> constructor <;> apply Fin.ext <;> omega
    rcases hends with ⟨hi, hj⟩
    subst Ki
    subst Kj
    right
    ext t
    change α ({ i := Ji, j := Jj, hij := Jh, ε := true } : SignedInterval n) t =
      - α ({ i := Ji, j := Jj, hij := Kh, ε := false } : SignedInterval n) t
    rw [α_eval, α_eval]
    simp [SignedInterval.sign]
  · simp +decide only [SignedInterval.sign] at hcw
    have hends : Ji = Ki ∧ Jj = Kj := by
      split_ifs at hcw <;> constructor <;> apply Fin.ext <;> omega
    rcases hends with ⟨hi, hj⟩
    subst Ki
    subst Kj
    left
    rfl

lemma An_is_crystallographic (n : ℕ) [NeZero n] : (An n).IsCrystallographic := by
  infer_instance



-- Note that the root pairing An is not irreducible. Indeed, the set of roots for A1 is {2e1, -2e1},
-- whose ℤ-span is a proper sub-module of M which remains invariant under the s_i's.
-- Similarly, the root pairing An is not a root system.

-- To fix this, we must base change to ℚ or ℝ
