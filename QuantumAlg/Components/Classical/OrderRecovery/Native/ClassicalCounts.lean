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

noncomputable section

/-- The two real selection arms share four copies and retain their other three coordinates. -/
lemma selectionEnvelope_eq_list (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) :
    selectionEnvelope model width = ResourcePool.ofList
      [.classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordUnary .copy width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordUnary .copy width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordUnary .copy width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordUnary .copy width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model)
          (.wordBinary .lessThan width)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .copy)),
        .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not))] := by
  cases model with
  | classical operations services =>
      have same := BitWord.Selected.operations_eq
        (execution := .classical operations services)
      change operations = BitWord.model at same
      cases same
      apply Multiset.ext.mpr
      intro event
      change ResourcePool.count event (selectionEnvelope _ width) = ResourcePool.count event _
      by_cases copied : Resource.Event.classicalOperation
          (model := .classical BitWord.model services) (.wordUnary .copy width) = event
      · subst event
        simp [BitWord.selectedCoordinate, selectionEnvelope, rejectionEvents, acceptanceEvents]
      by_cases compared : Resource.Event.classicalOperation
          (model := .classical BitWord.model services) (.wordBinary .lessThan width) = event
      · subst event
        simp [BitWord.selectedCoordinate, selectionEnvelope, rejectionEvents, acceptanceEvents]
      by_cases latched : Resource.Event.classicalOperation
          (model := .classical BitWord.model services) (.bit .copy) = event
      · subst event
        simp [BitWord.selectedCoordinate, selectionEnvelope, rejectionEvents, acceptanceEvents]
      by_cases stopped : Resource.Event.classicalOperation
          (model := .classical BitWord.model services) (.bit .not) = event
      · subst event
        simp [BitWord.selectedCoordinate, selectionEnvelope, rejectionEvents, acceptanceEvents]
      simp [BitWord.selectedCoordinate, selectionEnvelope, rejectionEvents, acceptanceEvents,
        copied, compared, latched, stopped]
  | quantum gates oracles operations services =>
      have same := BitWord.Selected.operations_eq
        (execution := .quantum gates oracles operations services)
      change operations = BitWord.model at same
      cases same
      apply Multiset.ext.mpr
      intro event
      change ResourcePool.count event (selectionEnvelope _ width) = ResourcePool.count event _
      by_cases copied : Resource.Event.classicalOperation
          (model := .quantum gates oracles BitWord.model services) (.wordUnary .copy width) = event
      · subst event
        simp [BitWord.selectedCoordinate, selectionEnvelope, rejectionEvents, acceptanceEvents]
      by_cases compared : Resource.Event.classicalOperation
          (model := .quantum gates oracles BitWord.model services)
          (.wordBinary .lessThan width) = event
      · subst event
        simp [BitWord.selectedCoordinate, selectionEnvelope, rejectionEvents, acceptanceEvents]
      by_cases latched : Resource.Event.classicalOperation
          (model := .quantum gates oracles BitWord.model services) (.bit .copy) = event
      · subst event
        simp [BitWord.selectedCoordinate, selectionEnvelope, rejectionEvents, acceptanceEvents]
      by_cases stopped : Resource.Event.classicalOperation
          (model := .quantum gates oracles BitWord.model services) (.bit .not) = event
      · subst event
        simp [BitWord.selectedCoordinate, selectionEnvelope, rejectionEvents, acceptanceEvents]
      simp [BitWord.selectedCoordinate, selectionEnvelope, rejectionEvents, acceptanceEvents,
        copied, compared, latched, stopped]

/-- The coordinatewise selection allowance contains seven classical operations. -/
lemma selectionEnvelope_classicalCount (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (selectionEnvelope model width) = 7 := by
  rw [selectionEnvelope_eq_list]
  simp [Resource.Event.classicalOperationWeight]

/-- The existing modular-power allowance has this exact total classical weight. -/
private lemma powerEnvelope_classicalCount (model : ExecutionModel) [BitWord.Selected model]
    (modulusWidth width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (Modular.NativePower.eventEnvelope model modulusWidth width) =
      2 * modulusWidth + 5 + 6 * width := by
  simp [Modular.NativePower.eventEnvelope, Modular.NativePower.exponentEnvelope,
    Modular.NativePower.bitEnvelope, Modular.NativePower.multiplyEnvelope,
    ConstantWord.envelope, ConstantWord.bitEnvelope, ConstantWord.shiftEvent,
    ConstantWord.incrementEvent, ResourcePool.scale, Resource.Event.classicalOperationWeight]
  omega

/-- Each visit allowance includes all actual candidate, power, validation and selection work. -/
lemma visitEnvelope_classicalCount (model : ExecutionModel) [BitWord.Selected model]
    (modulusWidth width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (visitEnvelope model modulusWidth width) = 2 * modulusWidth + 18 + 6 * width := by
  simp [visitEnvelope, candidateEvents, validationEvents, powerEnvelope_classicalCount,
    selectionEnvelope_classicalCount, Resource.Event.classicalOperationWeight]
  omega

/-- The padded decoder, denominator loader and three initialization writes are all counted. -/
lemma initializationEnvelope_classicalCount (model : ExecutionModel) [BitWord.Selected model]
    (modulusWidth width : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (initializationEnvelope model modulusWidth width) = 4 * width + 3 := by
  simp [initializationEnvelope, TerminalDecode.envelope, TerminalDecode.bitEnvelope,
    TerminalDecode.shiftEvent, TerminalDecode.incrementEvent, ConstantWord.envelope,
    ConstantWord.bitEnvelope, ConstantWord.shiftEvent, ConstantWord.incrementEvent,
    ResourcePool.scale, Resource.Event.classicalOperationWeight]
  omega

/-- Exact classical weight of the fixed independent recovery budget, including option packing. -/
lemma eventEnvelope_classicalCount (model : ExecutionModel) [BitWord.Selected model]
    (modulusWidth phaseBits : Nat) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (eventEnvelope model modulusWidth phaseBits) =
      4 * (phaseBits + 1) + 4 +
        2 * (phaseBits + 1) * (2 * modulusWidth + 18 + 6 * (phaseBits + 1)) := by
  simp only [eventEnvelope, ResourcePool.weightedCount_add,
    initializationEnvelope_classicalCount, ResourcePool.scale,
    ResourcePool.weightedCount_nsmul, visitEnvelope_classicalCount,
    ResourcePool.weightedCount_singleton, Resource.Event.classicalOperationWeight, Nat.mul_one]
  omega

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
