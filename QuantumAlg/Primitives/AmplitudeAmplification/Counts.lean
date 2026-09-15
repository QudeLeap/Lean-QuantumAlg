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

private theorem reflection_quantumSubroutineCount (n : Nat)
    (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label) (ZeroReflection.elementaryEventPool n) = 0 := by
  match n with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | extra + 4 =>
      simp only [ZeroReflection.elementaryEventPool, ResourcePool.count_add,
        ResourcePool.count_nsmul, ResourcePool.count_singleton]
      simp

/-- The complete actual circuit contains precisely the three source query families. -/
theorem code_quantumSubroutineCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) (path : (code M k).Path) (label : Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label) ((code M k).resourcePool path) =
      (if preparationEvent n = .quantumSubroutine label then 1 else 0) +
        k * ((if goodReflectionEvent n = .quantumSubroutine label then 1 else 0) +
          (if inversePreparationEvent n = .quantumSubroutine label then 1 else 0) +
          (if preparationEvent n = .quantumSubroutine label then 1 else 0)) := by
  rw [code_events]
  simp only [eventBudget, basisPreparationEvent, Native.unitaryEventPool, Native.stepEventPool,
    ResourcePool.count_add, ResourcePool.count_nsmul, ResourcePool.count_singleton,
    reflection_quantumSubroutineCount]
  simp

/-- One initial source call precedes the one call in each actual iterate. -/
theorem code_preparationCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) (path : (code M k).Path) :
    ResourcePool.count (preparationEvent n) ((code M k).resourcePool path) = k + 1 := by
  have count := code_quantumSubroutineCount M k path (preparationLabel n).quantum
  simpa [preparationEvent, inversePreparationEvent, goodReflectionEvent,
    Resource.SubroutineLabel.quantum, preparationLabel, inversePreparationLabel,
    goodReflectionLabel, Nat.add_comm] using count

/-- Each actual iterate contains precisely one inverse query. -/
theorem code_inversePreparationCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) (path : (code M k).Path) :
    ResourcePool.count (inversePreparationEvent n) ((code M k).resourcePool path) = k := by
  have count := code_quantumSubroutineCount M k path (inversePreparationLabel n).quantum
  simpa [preparationEvent, inversePreparationEvent, goodReflectionEvent,
    Resource.SubroutineLabel.quantum, preparationLabel, inversePreparationLabel,
    goodReflectionLabel] using count

/-- Each actual iterate contains precisely one source distinguishing reflection. -/
theorem code_goodReflectionCount {n : Nat} (M : IntrinsicAmplitudeAmplificationModel n)
    (k : Nat) (path : (code M k).Path) :
    ResourcePool.count (goodReflectionEvent n) ((code M k).resourcePool path) = k := by
  have count := code_quantumSubroutineCount M k path (goodReflectionLabel n).quantum
  simpa [preparationEvent, inversePreparationEvent, goodReflectionEvent,
    Resource.SubroutineLabel.quantum, preparationLabel, inversePreparationLabel,
    goodReflectionLabel] using count

end

end QuantumAlg.AmplitudeAmplification
