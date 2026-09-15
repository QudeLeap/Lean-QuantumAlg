/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Resources

/-!
# Cardinality of the actual raw-XGCD allowance

The six initialization operations, original public Euclidean fuel schedule,
fourteen-operation active allowance and three output copies are all retained.
Only the allowance has this exact size; inactive actual slots may emit less.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open ClassicalAlgorithms.NumberTheory

/-- The actual independent raw-engine allowance has its original linear cardinality. -/
theorem rawEnvelope_card (kind : ProblemKind) (width : Nat) :
    (rawEnvelope kind width).card = 28 * width + 23 := by
  simp [rawEnvelope, initializationEvents, activeEvents, coefficientUpdateEvents,
    rawOutputEvents, Euclid.gcdFuel, ResourcePool.scale, ResourcePool.ofList]
  omega

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
