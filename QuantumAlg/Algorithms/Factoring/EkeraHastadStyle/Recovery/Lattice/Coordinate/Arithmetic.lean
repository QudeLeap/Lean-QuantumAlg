/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Lattice.Coordinate.Readout
import Mathlib.Data.Int.ModEq

/-!
# Integer meaning of the actual lattice coordinate instructions

The real low-product and wrapping-subtraction word is congruent to the exact
integer target minus coefficient times source. Hence any integer values
represented by the incoming raw words produce the same source row operation.
This includes negative represented values and width zero; exact signed-range
facts belong to the existing source reducer invariant, not to a new caller
condition or a second arithmetic evaluator.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.Coordinate

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem low_multiply_subtract (width target coefficient source : Nat) :
    Int.ModEq (2 ^ width : Nat)
      (((target + 2 ^ width - (coefficient * source) % 2 ^ width) % 2 ^ width : Nat) : Int)
      ((target : Int) - (coefficient : Int) * (source : Int)) := by
  let capacity := 2 ^ width
  let lowProduct := (coefficient * source) % capacity
  have productBound : lowProduct ≤ target + capacity :=
    (Nat.le_of_lt (Nat.mod_lt _ (Nat.two_pow_pos width))).trans (Nat.le_add_left _ _)
  have lifted : ((target + capacity - lowProduct : Nat) : Int) =
      (target : Int) + (capacity : Int) - (lowProduct : Int) := by
    rw [Int.natCast_sub productBound, Int.natCast_add]
  have productMod : Int.ModEq (capacity : Int) (lowProduct : Int)
      ((coefficient : Int) * (source : Int)) := by
    have actual := Int.natCast_modEq_iff.mpr (Nat.mod_modEq (coefficient * source) capacity)
    simpa only [Int.natCast_mul] using actual
  have subtracted : Int.ModEq (capacity : Int)
      ((target + capacity - lowProduct : Nat) : Int)
      ((target : Int) - (coefficient : Int) * (source : Int)) := by
    rw [lifted]
    exact (Int.add_modEq_right (a := (target : Int)) (n := (capacity : Int))).sub productMod
  exact (Int.natCast_modEq_iff.mpr
    (Nat.mod_modEq (target + capacity - lowProduct) capacity)).trans subtracted

/-- The integer congruence belongs to the actual returned target word of the two instructions. -/
theorem nativeLattice_coordinate_intModEq
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) (store : Store ctx) :
    Int.ModEq (2 ^ width : Nat)
      (((storeStep coefficient source target store).read
        (.storage target.toCStorageRef)).toNat : Int)
      (((store.read (.storage target.toCStorageRef)).toNat : Int) -
        ((store.read coefficient).toNat : Int) * ((store.read source).toNat : Int)) := by
  rw [nativeLattice_coordinate_read]
  exact low_multiply_subtract width (store.read (.storage target.toCStorageRef)).toNat
    (store.read coefficient).toNat (store.read source).toNat

/-- Actual coordinate reduction transports the incoming integer representation invariant. -/
theorem nativeLattice_coordinate_represents
    (coefficient source : CInputRef ctx (.unsignedWord width))
    (target : CWriteRef ctx (.unsignedWord width)) (store : Store ctx)
    (targetValue coefficientValue sourceValue : Int)
    (targetRepresents : Int.ModEq (2 ^ width : Nat)
      ((store.read (.storage target.toCStorageRef)).toNat : Int) targetValue)
    (coefficientRepresents : Int.ModEq (2 ^ width : Nat)
      ((store.read coefficient).toNat : Int) coefficientValue)
    (sourceRepresents : Int.ModEq (2 ^ width : Nat)
      ((store.read source).toNat : Int) sourceValue) :
    Int.ModEq (2 ^ width : Nat)
      (((storeStep coefficient source target store).read
        (.storage target.toCStorageRef)).toNat : Int)
      (targetValue - coefficientValue * sourceValue) :=
  (nativeLattice_coordinate_intModEq coefficient source target store).trans
    (targetRepresents.sub (coefficientRepresents.mul sourceRepresents))

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Lattice.Coordinate
