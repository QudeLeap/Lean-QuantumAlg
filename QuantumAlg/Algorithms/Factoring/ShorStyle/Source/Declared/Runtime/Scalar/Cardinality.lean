/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Spec
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Scalar.Spec
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Budget
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Power.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Scope.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.Selection.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.HalfOrder.GCD.Adjacent.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Budget
import all QuantumAlg.Components.Classical.NumberTheory.GCD.EventCounts
import all QuantumAlg.Components.Classical.NumberTheory.FactorRange.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Components.Classical.TerminalDecode.Resources
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Scalar capacities of all original Shor recovery branches

The proof adds safe capacities for both native branches. All loop multiplicities
remain symbolic scalars. The source even-modulus exception is retained, and no
fixed instance, operand or gate list is unfolded to obtain a numerical count.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar

open ClassicalRoutines

noncomputable section

variable (model : ExecutionModel) [BitWord.Selected model]

omit [BitWord.Selected model] in
private lemma max_card_le_add (left right : ResourcePool model) :
    (ResourcePool.max left right).card ≤ left.card + right.card := by
  have dominated : ResourcePool.max left right ≤ left + right := by
    apply ResourcePool.max_le
    · apply ResourcePool.le_iff_count.mpr
      intro event
      rw [ResourcePool.count_add]
      exact Nat.le_add_right _ _
    · apply ResourcePool.le_iff_count.mpr
      intro event
      rw [ResourcePool.count_add]
      exact Nat.le_add_left _ _
  exact (Multiset.card_le_card dominated).trans_eq (Multiset.card_add left right)

private lemma constant_card (width : Nat) :
    (ConstantWord.envelope model width).card = 2 * width := by
  simp [ConstantWord.envelope, ConstantWord.bitEnvelope, ResourcePool.scale,
    ResourcePool.singleton, Nat.mul_comm]

private lemma decode_card (width : Nat) :
    (TerminalDecode.envelope (model := model) width).card = 2 * width := by
  simp [TerminalDecode.envelope, TerminalDecode.bitEnvelope, ResourcePool.scale,
    ResourcePool.singleton, Nat.mul_comm]

private lemma power_card (width exponentWidth : Nat) :
    (Modular.NativePower.eventEnvelope model width exponentWidth).card =
      2 * width + 5 + 6 * exponentWidth := by
  simp only [Modular.NativePower.eventEnvelope, Modular.NativePower.exponentEnvelope,
    Modular.NativePower.bitEnvelope, Modular.NativePower.multiplyEnvelope,
    Multiset.card_add, ResourcePool.scale, Multiset.card_nsmul, constant_card model,
    ResourcePool.singleton, Multiset.card_replicate]
  omega

private lemma order_selection_card (width : Nat) :
    (OrderRecovery.Native.selectionEnvelope model width).card ≤ 8 := by
  have bound := max_card_le_add model
    (ResourcePool.ofList (OrderRecovery.Native.rejectionEvents model width))
    (ResourcePool.ofList (OrderRecovery.Native.acceptanceEvents model width))
  simpa [OrderRecovery.Native.selectionEnvelope, OrderRecovery.Native.rejectionEvents,
    OrderRecovery.Native.acceptanceEvents, ResourcePool.ofList] using bound

private lemma order_visit_card (modulusWidth width : Nat) :
    (OrderRecovery.Native.visitEnvelope model modulusWidth width).card ≤
      2 * modulusWidth + 19 + 6 * width := by
  have selected := order_selection_card model width
  simp only [OrderRecovery.Native.visitEnvelope, Multiset.card_add, power_card model]
  simp only [OrderRecovery.Native.candidateEvents, OrderRecovery.Native.validationEvents,
    ResourcePool.ofList, Multiset.coe_card, List.length_cons, List.length_nil]
  omega

/-- Every prescribed continued-fraction visit obeys one width-only native scalar allowance. -/
lemma order_recovery_card_le (N : Nat) :
    (OrderRecovery.Native.eventEnvelope model (modulusBits N) (phaseBits N)).card ≤
      orderRecoveryEvents N := by
  have visits := Nat.mul_le_mul_left (2 * (phaseBits N + 1))
    (order_visit_card model (modulusBits N) (phaseBits N + 1))
  simp only [OrderRecovery.Native.eventEnvelope, OrderRecovery.Native.initializationEnvelope,
    Multiset.card_add, ResourcePool.scale, Multiset.card_nsmul, decode_card model,
    constant_card model, ResourcePool.singleton, Multiset.card_replicate]
  simp only [ResourcePool.ofList, Multiset.coe_card, List.length_cons, List.length_nil]
  unfold orderRecoveryEvents
  omega

private lemma adjacent_card (successor : Bool) (width : Nat) :
    (FactorRecovery.NativeAdjacentWord.eventEnvelope model successor width).card ≤ 3 := by
  cases successor <;>
    simp [FactorRecovery.NativeAdjacentWord.eventEnvelope, ResourcePool.singleton]

private lemma half_gcd_card (successor : Bool) (N : Nat) :
    (FactorRecovery.NativeHalfGCD.eventEnvelope model successor N).card ≤
      12 * (modulusBits N + 1) + 14 := by
  have adjacent := adjacent_card model successor (modulusBits N)
  simp only [FactorRecovery.NativeHalfGCD.eventEnvelope, Multiset.card_add,
    constant_card model, NumberTheory.GCD.gcdNativeEnvelope_card,
    ResourcePool.singleton, Multiset.card_replicate]
  omega

private lemma range_card (width : Nat) :
    (NumberTheory.FactorRange.eventBudget (model := model) width).card = 3 := rfl

private lemma half_factor_card (N : Nat) :
    (FactorRecovery.NativeHalfFactorScope.eventEnvelope model N).card ≤
      28 * (modulusBits N + 1) + 40 := by
  have left := half_gcd_card model false N
  have right := half_gcd_card model true N
  simp only [FactorRecovery.NativeHalfFactorScope.eventEnvelope,
    FactorRecovery.NativeHalfFactor.eventEnvelope, FactorRecovery.NativeHalfFactor.rightEnvelope,
    Multiset.card_add, constant_card model, range_card model]
  simp only [FactorRecovery.NativeHalfFactor.packBudget, ResourcePool.ofList,
    Multiset.coe_card, List.length_cons, List.length_nil]
  omega

private lemma reduction_card_le (N : Nat) :
    (FactorRecovery.NativeFactorTail.reduceEnvelope model N).card ≤ reductionEvents N := by
  have selected := half_factor_card model N
  simp only [FactorRecovery.NativeFactorTail.reduceEnvelope,
    FactorRecovery.NativeHalfPower.eventEnvelope, Multiset.card_add, power_card model,
    ResourcePool.singleton, Multiset.card_replicate]
  unfold reductionEvents
  omega

private lemma recovery_dispatch_card (N : Nat) :
    (FactorRecovery.NativeFactorTail.dispatchEnvelope model N).card ≤ reductionEvents N + 7 := by
  have reduction := reduction_card_le model N
  have checked := max_card_le_add model
    (FactorRecovery.NativeFactorTail.packBudget model N)
    (FactorRecovery.NativeFactorTail.reduceEnvelope model N)
  have dispatched := max_card_le_add model
    (FactorRecovery.NativeFactorTail.packBudget model N)
    (FactorRecovery.NativeFactorTail.checkedEnvelope model N)
  simp only [FactorRecovery.NativeFactorTail.checkedEnvelope, Multiset.card_add] at dispatched
  simp only [FactorRecovery.NativeFactorTail.packBudget,
    FactorRecovery.NativeFactorTail.guardEvents,
    ResourcePool.singleton, Multiset.card_replicate, ResourcePool.ofList, Multiset.coe_card,
    List.length_cons, List.length_nil] at checked dispatched
  simp only [FactorRecovery.NativeFactorTail.dispatchEnvelope,
    FactorRecovery.NativeFactorTail.checkedEnvelope, FactorRecovery.NativeFactorTail.packBudget,
    FactorRecovery.NativeFactorTail.guardEvents, ResourcePool.singleton, ResourcePool.ofList]
  omega

/-- The original known-modulus branch has a complete independent scalar native capacity. -/
lemma recovery_card_le (N : Nat) :
    (FactorRecovery.NativeFactorTail.eventEnvelope model N).card ≤ recoveryEvents N := by
  unfold FactorRecovery.NativeFactorTail.eventEnvelope recoveryEvents
  split
  · simp only [FactorRecovery.NativeFactorTail.evenEnvelope, Multiset.card_add,
      FactorRecovery.NativeFactorTail.packBudget, constant_card model,
      ResourcePool.singleton, Multiset.card_replicate]
    omega
  · have recovered := order_recovery_card_le model N
    have dispatch := recovery_dispatch_card model N
    simp only [FactorRecovery.NativeFactorTail.recoveredEnvelope, Multiset.card_add,
      ResourcePool.singleton, Multiset.card_replicate]
    omega

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Scalar
