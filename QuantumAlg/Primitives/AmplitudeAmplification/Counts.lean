/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.AmplitudeAmplification.Execution
import all QuantumAlg.Primitives.AmplitudeAmplification.Specification
import all QuantumAlg.Primitives.AmplitudeAmplification.Resources
import all QuantumAlg.Primitives.AmplitudeAmplification.Program.Resources
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Components.Oracle.ZeroReflection.Resources
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Exact source-query counts in the complete amplification run

The initial source preparation and all k actual iterates are read from the
same complete native event pool. The known zero reflection contributes only
elementary gates. Preparation, inverse and recognition remain distinct coordinates.
-/

namespace QuantumAlg.AmplitudeAmplification

noncomputable section

open AmplitudeAmplificationSource

private theorem reflection_oracleCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (coordinate : Coordinate) :
    ResourcePool.count (model := model M)
      (.oracle coordinate)
      (ZeroReflection.elementaryEventPool (Native.oracles M.preparation M.good) n) = 0 := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | extra + 4 =>
      simp only [ZeroReflection.elementaryEventPool, ResourcePool.count_add,
        ResourcePool.count_nsmul, ResourcePool.count_singleton]
      cases coordinate <;> simp

/-- The complete actual circuit contains precisely the three ordinary source query families. -/
theorem code_oracleCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) (path : (code M k).Path) (coordinate : Coordinate) :
    ResourcePool.count (model := model M)
      (.oracle coordinate) ((code M k).resourcePool path) =
      (if Coordinate.preparation = coordinate then 1 else 0) +
        k * ((if Coordinate.goodReflection = coordinate then 1 else 0) +
          (if Coordinate.inversePreparation = coordinate then 1 else 0) +
          (if Coordinate.preparation = coordinate then 1 else 0)) := by
  rw [code_events]
  simp only [eventBudget, Native.unitaryEventPool, Native.stepEventPool,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton,
    reflection_oracleCount]
  cases coordinate <;> simp

/-- One initial source call precedes the one call in each actual iterate. -/
theorem code_preparationCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) (path : (code M k).Path) :
    ResourcePool.count (model := model M)
      (.oracle .preparation) ((code M k).resourcePool path) = k + 1 := by
  simpa [Nat.add_comm] using code_oracleCount M k path .preparation

/-- Each actual iterate contains precisely one inverse query. -/
theorem code_inversePreparationCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) (path : (code M k).Path) :
    ResourcePool.count (model := model M)
      (.oracle .inversePreparation) ((code M k).resourcePool path) = k := by
  simpa using code_oracleCount M k path .inversePreparation

/-- Each actual iterate contains precisely one source distinguishing reflection. -/
theorem code_goodReflectionCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) (path : (code M k).Path) :
    ResourcePool.count (model := model M)
      (.oracle .goodReflection) ((code M k).resourcePool path) = k := by
  simpa using code_oracleCount M k path .goodReflection

/-- No coherent controlled query is requested by this source route. -/
theorem code_controlledGoodReflectionCount {n : Nat}
    (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) (path : (code M k).Path) :
    ResourcePool.count (model := model M)
      (.oracle .controlledGoodReflection) ((code M k).resourcePool path) = 0 := by
  simpa using code_oracleCount M k path .controlledGoodReflection

end

end QuantumAlg.AmplitudeAmplification
