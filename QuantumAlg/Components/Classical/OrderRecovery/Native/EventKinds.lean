/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Resources
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Budget
import all QuantumAlg.Components.Classical.TerminalDecode.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Resources

/-!
# Native recovery emits only its real classical operations

The independent coordinatewise allowance contains no quantum gate, query,
preparation or measurement. Every actual recovery path inherits these zero
coordinates from its already proved native event bound.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

noncomputable section

/-- Every coordinate outside classical operations is absent from the independent allowance. -/
theorem eventEnvelope_count_nonclassical {model : ExecutionModel} [BitWord.Selected model]
    (modulusWidth phaseBits : Nat) (event : Resource.Event model)
    (nonclassical : ∀ operation, Resource.Event.classicalOperation operation ≠ event) :
    ResourcePool.count event (eventEnvelope model modulusWidth phaseBits) = 0 := by
  simp [eventEnvelope, initializationEnvelope, visitEnvelope, selectionEnvelope,
    candidateEvents, validationEvents, rejectionEvents, acceptanceEvents,
    TerminalDecode.envelope, TerminalDecode.bitEnvelope, TerminalDecode.shiftEvent,
    TerminalDecode.incrementEvent, ConstantWord.envelope, ConstantWord.bitEnvelope,
    ConstantWord.shiftEvent, ConstantWord.incrementEvent, Modular.NativePower.eventEnvelope,
    Modular.NativePower.exponentEnvelope, Modular.NativePower.bitEnvelope,
    Modular.NativePower.multiplyEnvelope, ResourcePool.ofList_cons, ResourcePool.ofList_nil,
    nonclassical]

/-- The actual complete recovery adds no event outside its classical-operation coordinates. -/
theorem nativeRecovery_into_count_nonclassical {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {modulusWidth phaseBits : Nat}
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    (path : (into (model := model) spec base sample output).Path)
    (event : Resource.Event model)
    (nonclassical : ∀ operation, Resource.Event.classicalOperation operation ≠ event) :
    ResourcePool.count event
      ((into (model := model) spec base sample output).resourcePool path) = 0 := by
  have bound := ResourcePool.le_iff_count.mp
    (nativeRecovery_into_pool_le spec base sample output path) event
  rw [eventEnvelope_count_nonclassical modulusWidth phaseBits event nonclassical] at bound
  exact Nat.eq_zero_of_le_zero bound

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
