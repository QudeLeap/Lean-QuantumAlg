/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Budget
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Budget
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Resources
import all QuantumAlg.Components.Classical.NumberTheory.FactorRange.Resources
import all QuantumAlg.Components.Classical.TerminalDecode.Resources

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Resources
import all QuantumAlg.Components.Classical.NumberTheory.GCD.Step
import all QuantumAlg.Components.Classical.Modular.NativePower.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent.Resources

/-!
# Classical resource envelopes cannot charge quantum coordinates

Each parameter-indexed native envelope consists solely of the declaration-owned
classical operation coordinates. Proofs distribute symbolic sums, scales and
coordinatewise maxima; no instruction sequence or operand domain is evaluated.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar

open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] (event : Resource.Event model)
  (outside : ∀ coordinate, Resource.Event.classicalOperation coordinate ≠ event)

include outside

private theorem constant_zero (width : Nat) :
    ResourcePool.count event (ConstantWord.envelope model width) = 0 := by
  simp [ConstantWord.envelope, ConstantWord.bitEnvelope, ConstantWord.shiftEvent,
    ConstantWord.incrementEvent, ResourcePool.scale, outside]

private theorem decode_zero (width : Nat) :
    ResourcePool.count event (TerminalDecode.envelope (model := model) width) = 0 := by
  simp [TerminalDecode.envelope, TerminalDecode.bitEnvelope, TerminalDecode.shiftEvent,
    TerminalDecode.incrementEvent, ResourcePool.scale, outside]

private theorem first_zero (width : Nat) :
    ResourcePool.count event (FirstAccepted.nativeEnvelope model width) = 0 := by
  simp [FirstAccepted.nativeEnvelope, FirstAccepted.decisionEvents, FirstAccepted.copyEvents,
    ResourcePool.ofList, ResourcePool.count, outside]

private theorem gcd_zero (width : Nat) :
    ResourcePool.count event (NumberTheory.GCD.nativeEnvelope model width) = 0 := by
  have reverseOutside : ∀ label, event ≠ Resource.Event.classicalOperation label :=
    fun label => Ne.symm (outside label)
  simp_all [NumberTheory.GCD.nativeEnvelope, NumberTheory.GCD.initializationEvents,
    NumberTheory.GCD.remainderEvents, ResourcePool.scale, ResourcePool.ofList,
    ResourcePool.singleton, ResourcePool.count]

private theorem proposal_zero (width count : Nat) :
    ResourcePool.count event (Sampler.Proposal.scanEnvelope model width count) = 0 := by
  simp only [Sampler.Proposal.scanEnvelope, ResourcePool.count_scale,
    Sampler.Proposal.slotEnvelope, Sampler.Proposal.prefixEnvelope, ResourcePool.count_add,
    decode_zero event outside, first_zero event outside]
  simp [Sampler.Proposal.comparisonEvents, ResourcePool.ofList, ResourcePool.count, outside]

private theorem decision_zero (width : Nat) :
    ResourcePool.count event (Sampler.Decision.nativeEnvelope model width) = 0 := by
  have reverseOutside : ∀ label, event ≠ Resource.Event.classicalOperation label :=
    fun label => Ne.symm (outside label)
  simp only [Sampler.Decision.nativeEnvelope, Sampler.Decision.acceptedEnvelope,
    Sampler.Decision.resultEnvelope, ResourcePool.count_add, gcd_zero event outside]
  simp_all [Sampler.Decision.initializationEvents, Sampler.Decision.comparisonEvents,
    Sampler.Decision.unitEvents, Sampler.Decision.factorEvents, ResourcePool.ofList,
    ResourcePool.singleton, ResourcePool.count]

/-- Original random sampling and all residue preparation charge no non-classical coordinate. -/
theorem sampler_nonclassical_zero (N : Nat) :
    ResourcePool.count event (Sampler.Retained.nativeEnvelope model N) = 0 := by
  simp only [Sampler.Retained.nativeEnvelope, Sampler.Program.nativeEnvelope,
    ResourcePool.count_add, constant_zero event outside, proposal_zero event outside,
    decision_zero event outside]
  simp [ResourcePool.count_singleton, outside]

private theorem power_zero (width exponentWidth : Nat) :
    ResourcePool.count event (Modular.NativePower.eventEnvelope model width exponentWidth) = 0 := by
  simp only [Modular.NativePower.eventEnvelope, Modular.NativePower.exponentEnvelope,
    Modular.NativePower.bitEnvelope, Modular.NativePower.multiplyEnvelope,
    ResourcePool.count_add, ResourcePool.count_scale, constant_zero event outside]
  simp [ResourcePool.count_singleton, outside]

private theorem order_zero (modulusWidth phaseWidth : Nat) :
    ResourcePool.count event (OrderRecovery.Native.eventEnvelope model modulusWidth phaseWidth) =
      0 := by
  have reverseOutside : ∀ label, event ≠ Resource.Event.classicalOperation label :=
    fun label => Ne.symm (outside label)
  simp only [OrderRecovery.Native.eventEnvelope, OrderRecovery.Native.initializationEnvelope,
    OrderRecovery.Native.visitEnvelope, OrderRecovery.Native.selectionEnvelope,
    ResourcePool.count_add, ResourcePool.count_scale, ResourcePool.count_max,
    decode_zero event outside, constant_zero event outside, power_zero event outside]
  simp_all [OrderRecovery.Native.candidateEvents, OrderRecovery.Native.validationEvents,
    OrderRecovery.Native.rejectionEvents, OrderRecovery.Native.acceptanceEvents,
    ResourcePool.ofList, ResourcePool.singleton, ResourcePool.count]

private theorem adjacent_zero (successor : Bool) (width : Nat) :
    ResourcePool.count event (FactorRecovery.NativeAdjacentWord.eventEnvelope model successor
      width) = 0 := by
  cases successor <;> simp [FactorRecovery.NativeAdjacentWord.eventEnvelope, outside]

private theorem half_gcd_zero (successor : Bool) (N : Nat) :
    ResourcePool.count event (FactorRecovery.NativeHalfGCD.eventEnvelope model successor N) =
      0 := by
  simp only [FactorRecovery.NativeHalfGCD.eventEnvelope, ResourcePool.count_add,
    adjacent_zero event outside, constant_zero event outside, gcd_zero event outside]
  simp [ResourcePool.count_singleton, outside]

private theorem range_zero (width : Nat) :
    ResourcePool.count event (NumberTheory.FactorRange.eventBudget (model := model) width) = 0 := by
  simp [NumberTheory.FactorRange.eventBudget, NumberTheory.FactorRange.events,
    ResourcePool.ofList, ResourcePool.count, outside]

private theorem half_factor_zero (N : Nat) :
    ResourcePool.count event (FactorRecovery.NativeHalfFactorScope.eventEnvelope model N) = 0 := by
  simp only [FactorRecovery.NativeHalfFactorScope.eventEnvelope,
    FactorRecovery.NativeHalfFactor.eventEnvelope, FactorRecovery.NativeHalfFactor.rightEnvelope,
    ResourcePool.count_add, constant_zero event outside, half_gcd_zero event outside,
    range_zero event outside]
  simp [FactorRecovery.NativeHalfFactor.packBudget, ResourcePool.ofList, ResourcePool.count,
    outside]

private theorem reduce_zero (N : Nat) :
    ResourcePool.count event (FactorRecovery.NativeFactorTail.reduceEnvelope model N) = 0 := by
  simp only [FactorRecovery.NativeFactorTail.reduceEnvelope,
    FactorRecovery.NativeHalfPower.eventEnvelope, ResourcePool.count_add,
    power_zero event outside, half_factor_zero event outside]
  simp [ResourcePool.count_singleton, outside]

/-- Every real exceptional or full recovery branch has only classical native event coordinates. -/
theorem recovery_nonclassical_zero (N : Nat) :
    ResourcePool.count event (FactorRecovery.NativeFactorTail.eventEnvelope model N) = 0 := by
  have reverseOutside : ∀ label, event ≠ Resource.Event.classicalOperation label :=
    fun label => Ne.symm (outside label)
  simp only [FactorRecovery.NativeFactorTail.eventEnvelope]
  split
  · simp only [FactorRecovery.NativeFactorTail.evenEnvelope, ResourcePool.count_add,
      constant_zero event outside]
    simp_all [FactorRecovery.NativeFactorTail.packBudget, ResourcePool.count_singleton]
  · simp only [FactorRecovery.NativeFactorTail.recoveredEnvelope,
      FactorRecovery.NativeFactorTail.dispatchEnvelope,
      FactorRecovery.NativeFactorTail.checkedEnvelope,
      ResourcePool.count_add, ResourcePool.count_max, order_zero event outside,
      reduce_zero event outside]
    simp_all [FactorRecovery.NativeFactorTail.packBudget,
      FactorRecovery.NativeFactorTail.guardEvents,
      ResourcePool.ofList, ResourcePool.singleton, ResourcePool.count]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar
