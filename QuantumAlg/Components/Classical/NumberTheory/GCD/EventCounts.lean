/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.GCD.Resources

/-!
# Closed native coordinate allowances for the GCD schedule

These equalities evaluate the independent uniform allowance, rather than the
data-dependent trace of one input. The actual retained circuit is bounded by
that same pool. Inactive iterations contribute no executed events.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.GCD

noncomputable section

open ClassicalAlgorithms.NumberTheory

/-- The uniform allowance contains two copies per slot and three outside the loop. -/
theorem gcdNativeEnvelope_copy_count (model : ExecutionModel) [BitWord.Selected model] (width :
  Nat) :
    ResourcePool.count (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .copy width)))
      (nativeEnvelope model width) = 4 * width + 5 := by
  simp [BitWord.selectedCoordinate, nativeEnvelope, initializationEvents, remainderEvents,
    Euclid.gcdFuel]
  omega

/-- At most one actual native division is allowed per scheduled slot. -/
theorem gcdNativeEnvelope_divRem_count (model : ExecutionModel) [BitWord.Selected model] (width :
  Nat) :
    ResourcePool.count (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.divRem width width)))
      (nativeEnvelope model width) = 2 * width + 1 := by
  simp [BitWord.selectedCoordinate, nativeEnvelope, initializationEvents, remainderEvents,
    Euclid.gcdFuel]
  omega

/-- The initial comparison and at most one comparison per slot retain their native coordinate. -/
theorem gcdNativeEnvelope_equal_count (model : ExecutionModel) [BitWord.Selected model] (width :
  Nat) :
    ResourcePool.count (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal width)))
      (nativeEnvelope model width) = 2 * width + 2 := by
  simp [BitWord.selectedCoordinate, nativeEnvelope, initializationEvents, remainderEvents,
    Euclid.gcdFuel]
  omega

/-- The stored-condition negations have the same one-plus-slot allowance. -/
theorem gcdNativeEnvelope_not_count (model : ExecutionModel) [BitWord.Selected model] (width :
  Nat) :
    ResourcePool.count (.classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit
      .not)))
      (nativeEnvelope model width) = 2 * width + 2 := by
  simp [BitWord.selectedCoordinate, nativeEnvelope, initializationEvents, remainderEvents,
    Euclid.gcdFuel]
  omega

/-- Total event capacity is the sum of the four exact native coordinate allowances. -/
theorem gcdNativeEnvelope_card (model : ExecutionModel) [BitWord.Selected model] (width : Nat) :
    (nativeEnvelope model width).card = 10 * width + 10 := by
  simp [BitWord.selectedCoordinate, nativeEnvelope, initializationEvents, remainderEvents,
    Euclid.gcdFuel,
    ResourcePool.ofList, ResourcePool.scale, ResourcePool.singleton]
  omega

end

end QuantumAlg.ClassicalRoutines.NumberTheory.GCD
