import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.RootSystem.Basic

abbrev Zn (n : ℕ) [NeZero n] := Fin n -> ℤ
abbrev Zn_dual (n : ℕ) [NeZero n] := Module.Dual ℤ (Zn n)

def e_transpose {n : ℕ} (k : Fin n) [NeZero n] : Zn_dual n :=
  { toFun := fun t => t k
    map_add' := by
      intro t s
      rfl
    map_smul' := by
      intro a t
      rfl }

def Ae {n : ℕ} (k : Fin n) [NeZero n] : Zn n :=
  fun t =>
    if t = k then 2
    else if k + 1 = t ∨ t + 1 = k then -1
    else 0

structure SignedInterval (n : ℕ) where
  i : Fin n
  j : Fin n
  hij: i ≤ j
  ε : Bool

def SignedInterval.sign {n : ℕ} (J : SignedInterval n) : ℤ :=
  if J.ε then 1 else -1

def α {n : ℕ} (J : SignedInterval n) [NeZero n] : Zn n :=
  J.sign • Finset.sum (Finset.Icc J.i J.j) (fun k => Ae k)

def α_dual {n : ℕ} (J : SignedInterval n) [NeZero n] : Zn_dual n :=
  J.sign • Finset.sum (Finset.Icc J.i J.j) (fun k => e_transpose k)

def s {n : ℕ} (J : SignedInterval n) (K : SignedInterval n) [NeZero n] : SignedInterval n :=
  if h₀ : J.i = K.i ∧ J.j = K.j then
    { i := J.i, j := J.j, hij := J.hij, ε := false }
  else if h₁ : (J.i : ℕ) = (K.j : ℕ) + 1 then
    { i := K.i
      j := J.j
      hij := by
        have hKi : (K.i : ℕ) ≤ K.j := Fin.le_iff_val_le_val.mp K.hij
        have hJi : (J.i : ℕ) ≤ J.j := Fin.le_iff_val_le_val.mp J.hij
        exact Fin.le_iff_val_le_val.mpr (by omega)
      ε := true }
  else if h₂ : (K.i : ℕ) = (J.j : ℕ) + 1 then
    { i := J.i
      j := K.j
      hij := by
        have hJi : (J.i : ℕ) ≤ J.j := Fin.le_iff_val_le_val.mp J.hij
        have hKj : (K.i : ℕ) ≤ K.j := Fin.le_iff_val_le_val.mp K.hij
        exact Fin.le_iff_val_le_val.mpr (by omega)
      ε := true }
  else if h₃ : J.i = K.i ∧ J.j > K.j then
    { i := K.i
      j := J.j
      hij := by simpa [h₃.1] using J.hij
      ε := false }
  else if h₄ : J.i = K.i ∧ J.j < K.j then
    { i := J.i
      j := K.j
      hij := by simpa [h₄.1] using K.hij
      ε := true }
  else if h₅ : J.i < K.i ∧ J.j = K.j then
    { i := J.i
      j := J.j
      hij := by
        exact J.hij
      ε := false }
  else if h₆ : J.i > K.i ∧ J.j = K.j then
    { i := K.i
      j := K.j
      hij := by
        exact K.hij
      ε := true }
  else
    { i := J.i, j := J.j, hij := J.hij, ε := true }

noncomputable abbrev Zn_pairing (n : ℕ) [NeZero n] : Zn n →ₗ[ℤ] Zn_dual n →ₗ[ℤ] ℤ :=
  Module.Dual.eval ℤ (Zn n)

noncomputable def An (n : ℕ) [NeZero n] : RootPairing (SignedInterval n) ℤ (Zn n) (Zn_dual n) where
  toLinearMap := Zn_pairing n
  root :=
    { toFun := fun J => α (n := n) J
      inj' := by
        intro J K h
        sorry
    }
  coroot :=
    { toFun := fun J => α_dual (n := n) J
      inj' := by
        intro J K h
        sorry
    }
  root_coroot_two := by
    intro J
    simp[α, α_dual]
    sorry

  reflectionPerm := fun J =>
    { toFun := fun K => s (n := n) J K
      invFun := fun K => s (n := n) J K
      left_inv := by
        intro K
        simp only [s, gt_iff_lt, dite_eq_ite]
        sorry
      right_inv := by
        intro K
        sorry }
  reflectionPerm_root := sorry
  reflectionPerm_coroot := sorry
