/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Budget
import all QuantumAlg.Components.Classical.TerminalDecode.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Resources

/-!
# Numerical classical-operation allowance of native finite recovery

The coordinatewise selection allowance shares its word-copy coordinate:
four rejected-arm copies dominate the accepted arm's one copy. Its total is
therefore seven, including the remainder test and two latch operations.
The remaining terms count the existing decoder, constant loader, arithmetic,
modular validation and option packing allowances without changing them.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

/-- The two real selection arms share four copies and retain their other three coordinates. -/
theorem selectionEnvelope_eq_list (kind : ProblemKind) (width : Nat) :
    selectionEnvelope kind width = ResourcePool.ofList
      [.classicalOperation (.wordUnary .copy width),
        .classicalOperation (.wordUnary .copy width),
        .classicalOperation (.wordUnary .copy width),
        .classicalOperation (.wordUnary .copy width),
        .classicalOperation (.wordBinary .lessThan width),
        .classicalOperation (.bit .copy), .classicalOperation (.bit .not)] := by
  apply Multiset.ext.mpr
  intro event
  change ResourcePool.count event (selectionEnvelope kind width) = ResourcePool.count event _
  by_cases copied : Resource.Event.classicalOperation (.wordUnary .copy width) = event
  · subst event
    simp [selectionEnvelope, rejectionEvents, acceptanceEvents]
  by_cases compared : Resource.Event.classicalOperation (.wordBinary .lessThan width) = event
  · subst event
    simp [selectionEnvelope, rejectionEvents, acceptanceEvents]
  by_cases latched : Resource.Event.classicalOperation (.bit .copy) = event
  · subst event
    simp [selectionEnvelope, rejectionEvents, acceptanceEvents]
  by_cases stopped : Resource.Event.classicalOperation (.bit .not) = event
  · subst event
    simp [selectionEnvelope, rejectionEvents, acceptanceEvents]
  simp [selectionEnvelope, rejectionEvents, acceptanceEvents, copied, compared, latched, stopped]

/-- The coordinatewise selection allowance contains seven classical operations. -/
theorem selectionEnvelope_classicalCount (kind : ProblemKind) (width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (selectionEnvelope kind width) = 7 := by
  rw [selectionEnvelope_eq_list]
  simp [Resource.Event.classicalOperationWeight]

/-- The existing modular-power allowance has this exact total classical weight. -/
private theorem powerEnvelope_classicalCount (kind : ProblemKind) (modulusWidth width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (Modular.NativePower.eventEnvelope kind modulusWidth width) =
      2 * modulusWidth + 5 + 6 * width := by
  simp [Modular.NativePower.eventEnvelope, Modular.NativePower.exponentEnvelope,
    Modular.NativePower.bitEnvelope, Modular.NativePower.multiplyEnvelope,
    ConstantWord.envelope, ConstantWord.bitEnvelope, ConstantWord.shiftEvent,
    ConstantWord.incrementEvent, ResourcePool.scale, Resource.Event.classicalOperationWeight]
  omega

/-- Each visit allowance includes all actual candidate, power, validation and selection work. -/
theorem visitEnvelope_classicalCount (kind : ProblemKind) (modulusWidth width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (visitEnvelope kind modulusWidth width) = 2 * modulusWidth + 18 + 6 * width := by
  simp [visitEnvelope, candidateEvents, validationEvents, powerEnvelope_classicalCount,
    selectionEnvelope_classicalCount, Resource.Event.classicalOperationWeight]
  omega

/-- The padded decoder, denominator loader and three initialization writes are all counted. -/
theorem initializationEnvelope_classicalCount (kind : ProblemKind) (modulusWidth width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (initializationEnvelope kind modulusWidth width) = 4 * width + 3 := by
  simp [initializationEnvelope, TerminalDecode.envelope, TerminalDecode.bitEnvelope,
    TerminalDecode.shiftEvent, TerminalDecode.incrementEvent, ConstantWord.envelope,
    ConstantWord.bitEnvelope, ConstantWord.shiftEvent, ConstantWord.incrementEvent,
    ResourcePool.scale, Resource.Event.classicalOperationWeight]
  omega

/-- Exact classical weight of the fixed independent recovery budget, including option packing. -/
theorem eventEnvelope_classicalCount (kind : ProblemKind) (modulusWidth phaseBits : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (eventEnvelope kind modulusWidth phaseBits) =
      4 * (phaseBits + 1) + 4 +
        2 * (phaseBits + 1) * (2 * modulusWidth + 18 + 6 * (phaseBits + 1)) := by
  simp only [eventEnvelope, ResourcePool.weightedCount_add,
    initializationEnvelope_classicalCount, ResourcePool.scale,
    ResourcePool.weightedCount_nsmul, visitEnvelope_classicalCount,
    ResourcePool.weightedCount_singleton, Resource.Event.classicalOperationWeight, Nat.mul_one]
  omega

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
