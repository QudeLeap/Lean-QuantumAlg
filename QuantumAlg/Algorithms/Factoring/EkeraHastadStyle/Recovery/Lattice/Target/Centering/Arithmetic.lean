/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Target.Centering.Decision
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Coordinate.Arithmetic
import all QuantumAlg.Util.RSA.ShortLog.Target

/-!
# Integer meaning of the actual centered target

The real decision prefix and selected arithmetic instructions produce the
original centered-value formula modulo the word capacity. Zero is handled
first, and equality at half the modulus follows the nonnegative branch.
The internal separation and scratch-initialization premises describe the
temporary cells supplied by the enclosing workspace. No arithmetic range or
positive-width premise is needed for these actual word equations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetCentering

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Actual initialized decision cells select the original three unsigned word results. -/
theorem nativeLattice_targetCentering_read (refs : Refs ctx width)
    (separated : DecisionSeparated refs) (store : Store ctx)
    (scratchZero : (store.read (.storage refs.scratch.toCStorageRef)).toNat = 0) :
    (((step refs store).1).read (.storage refs.output.toCStorageRef)).toNat =
      if (store.read refs.preimage).toNat = 0 then 0
      else if (store.read refs.preimage).toNat < (store.read refs.modulus).toNat / 2 then
        (2 ^ width - (store.read refs.preimage).toNat) % 2 ^ width
      else ((store.read refs.modulus).toNat + 2 ^ width -
        (store.read refs.preimage).toNat) % 2 ^ width := by
  have sources := nativeLattice_targetCentering_decision_sources refs separated store
  have values := nativeLattice_targetCentering_decision_values refs separated store
  have zeroDecision :
      ((decisionStore refs store).read (.storage refs.isZero.toCStorageRef)).toBool =
        decide ((store.read refs.preimage).toNat = 0) :=
    values.2.1.trans (congrArg
      (fun value : Nat => decide ((store.read refs.preimage).toNat = value)) scratchZero)
  have belowDecision := values.2.2
  have selected := nativeLattice_targetCentering_step_store refs store
  dsimp only at selected
  by_cases zero : (store.read refs.preimage).toNat = 0
  · have zeroGuard :
        ((decisionStore refs store).read (.storage refs.isZero.toCStorageRef)).toBool = true :=
      zeroDecision.trans (decide_eq_true zero)
    rw [if_pos zeroGuard] at selected
    rw [if_pos zero]
    exact (congrArg (fun result : Store ctx =>
      (result.read (.storage refs.output.toCStorageRef)).toNat) selected).trans
      (nativeLattice_targetCentering_zero_read refs (decisionStore refs store))
  · have zeroGuard :
        ¬ ((decisionStore refs store).read (.storage refs.isZero.toCStorageRef)).toBool = true := by
      intro accepted
      exact zero (of_decide_eq_true (zeroDecision.symm.trans accepted))
    rw [if_neg zeroGuard] at selected
    rw [if_neg zero]
    by_cases below :
        (store.read refs.preimage).toNat < (store.read refs.modulus).toNat / 2
    · have belowGuard :
          ((decisionStore refs store).read
            (.storage refs.belowHalf.toCStorageRef)).toBool = true :=
        belowDecision.trans (decide_eq_true below)
      rw [if_pos belowGuard] at selected
      rw [if_pos below]
      exact (congrArg (fun result : Store ctx =>
        (result.read (.storage refs.output.toCStorageRef)).toNat) selected).trans
        ((nativeLattice_targetCentering_negate_read refs (decisionStore refs store)).trans
          (congrArg (fun value : Nat => (2 ^ width - value) % 2 ^ width)
            (congrArg CShape.Value.toNat sources.1)))
    · have belowGuard :
          ¬ ((decisionStore refs store).read
            (.storage refs.belowHalf.toCStorageRef)).toBool = true := by
        intro accepted
        exact below (of_decide_eq_true (belowDecision.symm.trans accepted))
      rw [if_neg belowGuard] at selected
      rw [if_neg below]
      exact (congrArg (fun result : Store ctx =>
        (result.read (.storage refs.output.toCStorageRef)).toNat) selected).trans
        ((nativeLattice_targetCentering_subtract_read refs (decisionStore refs store)).trans
          (congrArg₂ (fun modulus preimage : Nat =>
            (modulus + 2 ^ width - preimage) % 2 ^ width)
            (congrArg CShape.Value.toNat sources.2)
            (congrArg CShape.Value.toNat sources.1)))

/-- The returned actual word represents the unique original centered-value formula. -/
theorem nativeLattice_targetCentering_intModEq (refs : Refs ctx width)
    (separated : DecisionSeparated refs) (store : Store ctx)
    (scratchZero : (store.read (.storage refs.scratch.toCStorageRef)).toNat = 0) :
    Int.ModEq (2 ^ width : Nat)
      ((((step refs store).1).read (.storage refs.output.toCStorageRef)).toNat : Int)
      (RSA.ShortLogTarget.centeredValue
        (store.read refs.preimage).toNat (store.read refs.modulus).toNat) := by
  rw [nativeLattice_targetCentering_read refs separated store scratchZero]
  unfold RSA.ShortLogTarget.centeredValue
  by_cases zero : (store.read refs.preimage).toNat = 0
  · simp only [if_pos zero]
    exact Int.ModEq.refl 0
  · simp only [if_neg zero]
    by_cases below :
        (store.read refs.preimage).toNat < (store.read refs.modulus).toNat / 2
    · simp only [if_pos below]
      have arithmetic := Coordinate.low_multiply_subtract width 0 1
        (store.read refs.preimage).toNat
      rw [Nat.one_mul, Nat.mod_eq_of_lt (store.read refs.preimage).toNat_lt,
        Nat.zero_add] at arithmetic
      simpa only [Nat.cast_zero, Nat.cast_one, one_mul, zero_sub] using arithmetic
    · simp only [if_neg below]
      have arithmetic := Coordinate.low_multiply_subtract width
        (store.read refs.modulus).toNat 1 (store.read refs.preimage).toNat
      rw [Nat.one_mul, Nat.mod_eq_of_lt (store.read refs.preimage).toNat_lt] at arithmetic
      simpa only [Nat.cast_one, one_mul] using arithmetic

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.TargetCentering
