import Mathlib.Topology.Basic
import Mathlib.Tactic
/-
Copyright (c) 2026 Antoine de Saint Germain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine de Saint Germain
-/

/-- Basic definitions used in the root system development. -/
theorem identity (a b : ℤ) : (a+b)^2 = a^2 + 2*a*b + b^2 := by
  ring

theorem second_identity (a b : ℤ) : (a-b)^2 = a^2 - 2*a*b + b^2 := by
  ring
