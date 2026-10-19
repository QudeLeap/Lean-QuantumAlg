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

private lemma reflection_oracleCount (n : Nat)
    (coordinate : Coordinate) :
    ResourcePool.count (model := model n)
      (.oracle coordinate)
      (ZeroReflection.elementaryEventPool (Native.oracles n) n) = 0 := by
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
lemma code_oracleCount (n : Nat)
    (k : Nat) (path : (code n k).Path) (coordinate : Coordinate) :
    ResourcePool.count (model := model n)
      (.oracle coordinate) ((code n k).resourcePool path) =
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
lemma code_preparationCount (n : Nat)
    (k : Nat) (path : (code n k).Path) :
    ResourcePool.count (model := model n)
      (.oracle .preparation) ((code n k).resourcePool path) = k + 1 := by
  simpa [Nat.add_comm] using code_oracleCount n k path .preparation

/-- Each actual iterate contains precisely one inverse query. -/
lemma code_inversePreparationCount (n : Nat)
    (k : Nat) (path : (code n k).Path) :
    ResourcePool.count (model := model n)
      (.oracle .inversePreparation) ((code n k).resourcePool path) = k := by
  simpa using code_oracleCount n k path .inversePreparation

/-- Each actual iterate contains precisely one source distinguishing reflection. -/
lemma code_goodReflectionCount (n : Nat)
    (k : Nat) (path : (code n k).Path) :
    ResourcePool.count (model := model n)
      (.oracle .goodReflection) ((code n k).resourcePool path) = k := by
  simpa using code_oracleCount n k path .goodReflection

/-- No coherent controlled query is requested by this source route. -/
lemma code_controlledGoodReflectionCount (n : Nat)
    (k : Nat) (path : (code n k).Path) :
    ResourcePool.count (model := model n)
      (.oracle .controlledGoodReflection) ((code n k).resourcePool path) = 0 := by
  simpa using code_oracleCount n k path .controlledGoodReflection

end

end QuantumAlg.AmplitudeAmplification
