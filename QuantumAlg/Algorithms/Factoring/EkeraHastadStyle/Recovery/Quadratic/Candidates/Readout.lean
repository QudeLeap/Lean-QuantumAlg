/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Operations

/-!
# Exact reads of the actual quadratic arithmetic instructions

Widening preserves the original short-log word. The following instruction
equations expose the real modular arithmetic; their capacity conditions are
the internal consequences of the source word bounds, to be discharged by
the candidate pipeline. They impose no initialization condition on its cells.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The actual resize retains every bit of the original short logarithm. -/
lemma nativeQuadratic_widen_read (input : CInputRef ctx (.unsignedWord width))
    (refs : Refs ctx width) (store : Store ctx) :
    ((store.applyOp (widenOp input refs)).read (.storage refs.center.toCStorageRef)).toNat =
      (store.read input).toNat := by
  change ((store.applyOp (widenOp input refs)).read
    (.storage (widenOp input refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  change (store.read input).toNat % 2 ^ RSA.quadraticWordWidth width = _
  exact Nat.mod_eq_of_lt ((store.read input).toNat_lt.trans_le
    (Nat.pow_le_pow_right (by decide) (by unfold RSA.quadraticWordWidth; omega)))

/-- The actual increment gives the exact source center when its established word bound holds. -/
lemma nativeQuadratic_center_read_of_fits (refs : Refs ctx width) (store : Store ctx)
    (fits : (store.read (.storage refs.center.toCStorageRef)).toNat + 1 <
      2 ^ RSA.quadraticWordWidth width) :
    ((store.applyOp (centerOp refs)).read (.storage refs.center.toCStorageRef)).toNat =
      (store.read (.storage refs.center.toCStorageRef)).toNat + 1 := by
  change ((store.applyOp (centerOp refs)).read
    (.storage (centerOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  exact Nat.mod_eq_of_lt fits

/-- The actual word multiplication retains the complete center square at the proved capacity. -/
lemma nativeQuadratic_square_read_of_fits (refs : Refs ctx width) (store : Store ctx)
    (fits : (store.read (.storage refs.center.toCStorageRef)).toNat ^ 2 <
      2 ^ RSA.quadraticWordWidth width) :
    ((store.applyOp (squareOp refs)).read (.storage refs.root.toCStorageRef)).toNat =
      (store.read (.storage refs.center.toCStorageRef)).toNat ^ 2 := by
  change ((store.applyOp (squareOp refs)).read
    (.storage (squareOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  change ((store.read (.storage refs.center.toCStorageRef)).toNat *
    (store.read (.storage refs.center.toCStorageRef)).toNat) %
      2 ^ RSA.quadraticWordWidth width = _
  rw [← pow_two]
  exact Nat.mod_eq_of_lt fits

/-- The actual final addition materializes the exact upper candidate at the proved capacity. -/
lemma nativeQuadratic_second_read_of_fits (refs : Refs ctx width) (store : Store ctx)
    (fits : (store.read (.storage refs.center.toCStorageRef)).toNat +
      (store.read (.storage refs.root.toCStorageRef)).toNat < 2 ^ RSA.quadraticWordWidth width) :
    ((store.applyOp (secondOp refs)).read (.storage refs.second.toCStorageRef)).toNat =
      (store.read (.storage refs.center.toCStorageRef)).toNat +
        (store.read (.storage refs.root.toCStorageRef)).toNat := by
  change ((store.applyOp (secondOp refs)).read
    (.storage (secondOp refs).outputRef.toCStorageRef)).toNat = _
  rw [Store.read_applyOp_output]
  exact Nat.mod_eq_of_lt fits

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
