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

def s {n : ℕ} (J: SignedInterval n) (K: SignedInterval n) : SignedInterval n :=
  if J.i = K.i ∧ J.j = K.j then (SignedInterval n).mk J.i J.j J.hij false
  else SignedInterval n J.i J.j J.hij true

-- def An (n : ℕ) [NeZero n] : RootPairing (SignedInterval n) ℤ (Zn n) (Zn_dual n) where
