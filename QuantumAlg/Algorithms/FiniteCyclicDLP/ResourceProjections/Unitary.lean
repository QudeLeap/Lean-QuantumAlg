/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Construction

/-!
# Pure event projections of unitary circuits

Literal gate and classical-operation classifiers act on the native event
pool. Their additive and singleton laws give the exact structural QFT
projections without depending on allocation, recovery or repetition programs.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical

noncomputable section

/-- Boolean classifier for literal elementary-gate events.  Opaque quantum
subroutines, including `U_x`, are deliberately excluded. -/
def isElementaryGate : Resource.Event .quantum → Bool
  | .gate _ => true
  | _ => false

/-- Aggregate multiplicity of literal gate leaves in a strict quantum event
pool. -/
def elementaryGateCard (pool : ResourcePool .quantum) : Nat :=
  Multiset.countP (fun event => isElementaryGate event) pool

/-- Boolean classifier for literal typed classical operations. -/
def isClassicalOperation : Resource.Event .quantum → Bool
  | .classicalOperation _ => true
  | _ => false

/-- Aggregate multiplicity of literal classical-operation events in a strict
quantum event pool.  Classical subroutines and all quantum events are excluded. -/
def classicalOperationCard (pool : ResourcePool .quantum) : Nat :=
  Multiset.countP (fun event => isClassicalOperation event) pool

private theorem countP_isElementaryGate_singleton
    (event : Resource.Event .quantum) :
    Multiset.countP (fun current => isElementaryGate current) {event} =
      if isElementaryGate event then 1 else 0 := by
  change Multiset.countP (fun current => isElementaryGate current)
      (event ::ₘ 0) = _
  rw [Multiset.countP_cons]
  simp

private theorem countP_isClassicalOperation_singleton
    (event : Resource.Event .quantum) :
    Multiset.countP (fun current => isClassicalOperation current) {event} =
      if isClassicalOperation event then 1 else 0 := by
  change Multiset.countP (fun current => isClassicalOperation current)
      (event ::ₘ 0) = _
  rw [Multiset.countP_cons]
  simp

@[simp] theorem elementaryGateCard_zero :
    elementaryGateCard (0 : ResourcePool .quantum) = 0 := by
  simp [elementaryGateCard]

@[simp] theorem elementaryGateCard_add
    (left right : ResourcePool .quantum) :
    elementaryGateCard (left + right) =
      elementaryGateCard left + elementaryGateCard right := by
  simp [elementaryGateCard]

@[simp] theorem elementaryGateCard_scale
    (multiplicity : Nat) (pool : ResourcePool .quantum) :
    elementaryGateCard (ResourcePool.scale multiplicity pool) =
      multiplicity * elementaryGateCard pool := by
  simp [elementaryGateCard, ResourcePool.scale]

@[simp] theorem elementaryGateCard_nsmul
    (multiplicity : Nat) (pool : ResourcePool .quantum) :
    elementaryGateCard (multiplicity • pool) =
      multiplicity * elementaryGateCard pool := by
  simp [elementaryGateCard]

@[simp] theorem elementaryGateCard_singleton_gate
    (label : Resource.GateLabel) (multiplicity : Nat) :
    elementaryGateCard (ResourcePool.singleton (.gate label) multiplicity) =
      multiplicity := by
  unfold elementaryGateCard ResourcePool.singleton
  rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
  rw [countP_isElementaryGate_singleton]
  simp [isElementaryGate]

/-- Any non-gate singleton contributes zero elementary gates. -/
theorem elementaryGateCard_singleton_nonGate
    (event : Resource.Event .quantum)
    (notGate : ∀ label, event ≠ .gate label)
    (multiplicity : Nat) :
    elementaryGateCard (ResourcePool.singleton event multiplicity) = 0 := by
  cases event with
  | gate label => exact (notGate label rfl).elim
  | classicalOperation label =>
      unfold elementaryGateCard ResourcePool.singleton
      rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
      rw [countP_isElementaryGate_singleton]
      simp [isElementaryGate]
  | classicalSubroutine label =>
      unfold elementaryGateCard ResourcePool.singleton
      rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
      rw [countP_isElementaryGate_singleton]
      simp [isElementaryGate]
  | preparation label =>
      unfold elementaryGateCard ResourcePool.singleton
      rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
      rw [countP_isElementaryGate_singleton]
      simp [isElementaryGate]
  | measurement label =>
      unfold elementaryGateCard ResourcePool.singleton
      rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
      rw [countP_isElementaryGate_singleton]
      simp [isElementaryGate]
  | quantumSubroutine label =>
      unfold elementaryGateCard ResourcePool.singleton
      rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
      rw [countP_isElementaryGate_singleton]
      simp [isElementaryGate]

@[simp] theorem classicalOperationCard_zero :
    classicalOperationCard (0 : ResourcePool .quantum) = 0 := by
  simp [classicalOperationCard]

@[simp] theorem classicalOperationCard_add
    (left right : ResourcePool .quantum) :
    classicalOperationCard (left + right) =
      classicalOperationCard left + classicalOperationCard right := by
  simp [classicalOperationCard]

@[simp] theorem classicalOperationCard_scale
    (multiplicity : Nat) (pool : ResourcePool .quantum) :
    classicalOperationCard (ResourcePool.scale multiplicity pool) =
      multiplicity * classicalOperationCard pool := by
  simp [classicalOperationCard, ResourcePool.scale]

@[simp] theorem classicalOperationCard_nsmul
    (multiplicity : Nat) (pool : ResourcePool .quantum) :
    classicalOperationCard (multiplicity • pool) =
      multiplicity * classicalOperationCard pool := by
  simp [classicalOperationCard]

@[simp] theorem classicalOperationCard_singleton_classicalOperation
    (label : Resource.ClassicalOpLabel) (multiplicity : Nat) :
    classicalOperationCard
        (ResourcePool.singleton (.classicalOperation label) multiplicity) =
      multiplicity := by
  unfold classicalOperationCard ResourcePool.singleton
  rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
  rw [countP_isClassicalOperation_singleton]
  simp [isClassicalOperation]

/-- Any singleton outside the literal classical-operation constructor
contributes zero to the classical projection. -/
theorem classicalOperationCard_singleton_nonClassical
    (event : Resource.Event .quantum)
    (notClassical : ∀ label, event ≠ .classicalOperation label)
    (multiplicity : Nat) :
    classicalOperationCard (ResourcePool.singleton event multiplicity) = 0 := by
  cases event with
  | classicalOperation label => exact (notClassical label rfl).elim
  | classicalSubroutine label =>
      unfold classicalOperationCard ResourcePool.singleton
      rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
      rw [countP_isClassicalOperation_singleton]
      simp [isClassicalOperation]
  | gate label =>
      unfold classicalOperationCard ResourcePool.singleton
      rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
      rw [countP_isClassicalOperation_singleton]
      simp [isClassicalOperation]
  | preparation label =>
      unfold classicalOperationCard ResourcePool.singleton
      rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
      rw [countP_isClassicalOperation_singleton]
      simp [isClassicalOperation]
  | measurement label =>
      unfold classicalOperationCard ResourcePool.singleton
      rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
      rw [countP_isClassicalOperation_singleton]
      simp [isClassicalOperation]
  | quantumSubroutine label =>
      unfold classicalOperationCard ResourcePool.singleton
      rw [← Multiset.nsmul_singleton, Multiset.countP_nsmul]
      rw [countP_isClassicalOperation_singleton]
      simp [isClassicalOperation]

/-- Literal gate count of one structural QFT in the strict event ledger. -/
theorem qftCircuit_elementaryGateCard (n : Nat) :
    elementaryGateCard (QFTCircuit n).eventCost =
      n + n.choose 2 + n / 2 := by
  rw [QFTCircuit_eventCost_eq]
  simp

/-- The structural QFT contributes no literal classical operations. -/
theorem qftCircuit_classicalOperationCard_zero (n : Nat) :
    classicalOperationCard (QFTCircuit n).eventCost = 0 := by
  rw [QFTCircuit_eventCost_eq]
  simp [classicalOperationCard_singleton_nonClassical]

end

end QuantumAlg.FiniteCyclicDLP.Canonical
