/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.QueryModel.Recovery
import all QuantumAlg.Core.Execution.Measurement.Cells.Borrowed
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Borrowed.Support
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Components.Classical.EllipticCurve.Representation.Model

/-!
# Original public points on every actual recovery prefix

Every added bank or retained cell leaves the original borrowed observation
intact. Complete borrowed restoration supplies a supported original input
for every positive actual output block. Hence all real recovery prefixes
read the prescribed affine public points. No support premise about
unrelated stores or hypothetical execution states is required.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery

noncomputable section

open Execution ClassicalRoutines.EllipticCurve
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private lemma ownedTail_read {ctx : RuntimeCtx .quantum}
    (key : StorageKey) {count : Nat} (layout : QuantumLayout count)
    (fresh : key ∉ ctx.keys) (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (store : Store (ctx.addOwnedLayout key layout fresh disjoint)) {shape : CShape}
    (input : CInputRef ctx shape) :
    (Store.mk store.cells.2).read input =
      store.read (input.underOwnedLayout key layout fresh disjoint) := by
  induction input with
  | storage => rfl
  | product first second firstIH secondIH =>
      exact congrArg₂ CShape.Value.product firstIH secondIH
  | fixedVector entries entriesIH =>
      exact congrArg CShape.Value.fixedVector (funext entriesIH)
  | first source sourceIH => exact congrArg CShape.Value.first sourceIH
  | second source sourceIH => exact congrArg CShape.Value.second sourceIH
  | vectorGet source index sourceIH => exact congrArg (fun value => value.get index) sourceIH
  | bitsGet source index sourceIH => exact congrArg (fun value => value.bitGet index) sourceIH
  | wordBitGet source index sourceIH =>
      exact congrArg (fun value => value.wordBitGet index) sourceIH

private def samplingOriginal (I : ECDLPInstance E)
    (store : Store (Sampling.Reuse.context I)) : Store (Sampling.pre I) :=
  ⟨(MeasurementCells.originalStore 2 (Sampling.sampleWidth I)
    (⟨store.cells.2⟩ : Store (Sampling.post I))).cells.2⟩

private lemma samplingOriginal_read (I : ECDLPInstance E)
    (store : Store (Sampling.Reuse.context I)) {shape : CShape}
    (input : CInputRef (Sampling.pre I) shape) :
    (samplingOriginal I store).read input = store.read (originalInput I input) := by
  have retained := Store.retainedTail_read (Sampling.post I).canonicalFreshKey (.finite 2)
    (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.post I)) store
    (MeasurementCells.liftInput 2
      (input.underOwnedLayout (Sampling.pre I).canonicalFreshKey (layout I)
        (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.pre I)) (Sampling.bankDisjoint I))
      (Sampling.sampleWidth I))
  have measured := MeasurementCells.originalStore_read 2 (Sampling.sampleWidth I)
    (⟨store.cells.2⟩ : Store (Sampling.post I))
    (input.underOwnedLayout (Sampling.pre I).canonicalFreshKey (layout I)
      (RuntimeCtx.runtimeCtx_canonicalFreshKey_fresh (Sampling.pre I)) (Sampling.bankDisjoint I))
  exact (ownedTail_read _ _ _ _ _ input).trans (measured.trans retained)

private lemma samplingOriginal_borrowed (I : ECDLPInstance E)
    (store : Store (Sampling.Reuse.context I)) :
    HEq store.readBorrowedClassical (samplingOriginal I store).readBorrowedClassical := by
  exact (show HEq store.readBorrowedClassical
    (Store.mk store.cells.2 : Store (Sampling.post I)).readBorrowedClassical from by rfl).trans
    ((MeasurementCells.originalStore_borrowed 2 (Sampling.sampleWidth I)
      (⟨store.cells.2⟩ : Store (Sampling.post I))).trans (by rfl))

private def persistentTail {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width scalar : Nat) (store : Store (persistentCtx ctx width scalar)) : Store ctx :=
  ⟨store.cells.2.2.2.2.2.2.2⟩

private lemma persistentTail_borrowed {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width scalar : Nat) (store : Store (persistentCtx ctx width scalar)) :
    HEq store.readBorrowedClassical (persistentTail width scalar store).readBorrowedClassical := by
  rfl

private def persistentOriginal (I : ECDLPInstance E)
    (store : Store (persistentCtx (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I))) :
    Store (Sampling.Reuse.context I) := persistentTail (fieldWidth E) (scalarWidth I) store

private lemma persistentOriginal_read (I : ECDLPInstance E)
    (store : Store (persistentCtx (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)))
    {shape : CShape} (input : CInputRef (Sampling.Reuse.context I) shape) :
    (persistentOriginal I store).read input =
      store.read (persistentInput (fieldWidth E) (scalarWidth I) input) := by
  unfold persistentInput retainedInput
  erw [← Store.retainedTail_read, ← Store.retainedTail_read, ← Store.retainedTail_read,
    ← Store.retainedTail_read, ← Store.retainedTail_read, ← Store.retainedTail_read,
    ← Store.retainedTail_read]
  rfl

private lemma borrowed_transport_heq {model : ExecutionModel}
    {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) (value : post.borrowedClassicalShape.Value) :
    HEq (code.borrowedClassicalValueTransport value) value := by
  exact ((Equiv.cast_eq_iff_heq
    (congrArg CShape.Value code.borrowedClassicalShape_preserved)).mp rfl).symm

private lemma inputStore_eq_of_borrowed (I : ECDLPInstance E)
    (store : Store (Sampling.pre I))
    (same : store.readBorrowedClassical = (Runtime.Context.inputStore I).readBorrowedClassical) :
    store = Runtime.Context.inputStore I := by
  obtain ⟨⟨target, base, empty⟩⟩ := store
  cases empty
  change CShape.Value.product target (.product base .unit) =
    CShape.Value.product (Runtime.Context.targetValue I)
      (.product (Runtime.Context.baseValue I) .unit) at same
  cases same
  rfl

/-- Every positive actual prefix reads the two original public point values. -/
lemma ecdlpRecovery_prefix_points (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State (Sampling.pre I) Reference
      ((Sampling.executionModel I).HiddenState × History))
    (admitted : ∀ entry, 0 < (initial.block entry).mass → entry.1 = Runtime.Context.inputStore I)
    (prefixCode : Circuit (Sampling.executionModel I) (Sampling.pre I)
      (persistentCtx (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)))
    (record : Store (persistentCtx (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)) ×
      ((Sampling.executionModel I).HiddenState × (History × prefixCode.Path)))
    (positive : 0 < ((prefixCode.execute (Sampling.sourceEnvironment I A) Reference initial).block
      record).mass) :
    record.1.read (persistentInput (fieldWidth E) (scalarWidth I) (baseInput I)) =
        Runtime.Context.baseValue I ∧
      record.1.read (persistentInput (fieldWidth E) (scalarWidth I) (targetInput I)) =
        Runtime.Context.targetValue I := by
  have restored := prefixCode.borrowedRestored_of_noBorrowedQuantum
    (Sampling.sourceEnvironment I A) (by rfl) Reference initial
  obtain ⟨previous, present, same⟩ := prefixCode.borrowedRestored_supported_initial
    Reference initial _ restored record positive
  rw [admitted previous present] at same
  have tailBorrowed := persistentTail_borrowed (fieldWidth E) (scalarWidth I) record.1
  have original := (heq_of_eq same).trans
    ((borrowed_transport_heq prefixCode record.1.readBorrowedClassical).trans
      (tailBorrowed.trans (samplingOriginal_borrowed I (persistentOriginal I record.1))))
  have storeEq := inputStore_eq_of_borrowed I
    (samplingOriginal I (persistentOriginal I record.1)) (eq_of_heq original.symm)
  constructor
  · have readBase :=
      samplingOriginal_read I (persistentOriginal I record.1) (Runtime.Context.baseRef I)
    exact (persistentOriginal_read I record.1 (baseInput I)).symm.trans
      (readBase.symm.trans (by rw [storeEq]; exact Runtime.Context.inputStore_base I))
  · have readTarget :=
      samplingOriginal_read I (persistentOriginal I record.1) (Runtime.Context.targetRef I)
    exact (persistentOriginal_read I record.1 (targetInput I)).symm.trans
      (readTarget.symm.trans (by rw [storeEq]; exact Runtime.Context.inputStore_target I))

/-- Every actual positive prefix has the original complete point representations. -/
lemma ecdlpRecovery_prefix_represents (I : ECDLPInstance E) (A : Access I)
    {Reference : Register} {History : Type} [Fintype History]
    (initial : State (Sampling.pre I) Reference
      ((Sampling.executionModel I).HiddenState × History))
    (admitted : ∀ entry, 0 < (initial.block entry).mass → entry.1 = Runtime.Context.inputStore I)
    (prefixCode : Circuit (Sampling.executionModel I) (Sampling.pre I)
      (persistentCtx (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)))
    (record : Store (persistentCtx (Sampling.Reuse.context I) (fieldWidth E) (scalarWidth I)) ×
      ((Sampling.executionModel I).HiddenState × (History × prefixCode.Path)))
    (positive : 0 < ((prefixCode.execute (Sampling.sourceEnvironment I A) Reference initial).block
      record).mass) :
    PointRepresents (curve E)
        (record.1.read (persistentInput (fieldWidth E) (scalarWidth I) (baseInput I)))
        I.basePoint.toMathlib ∧
      PointRepresents (curve E)
        (record.1.read (persistentInput (fieldWidth E) (scalarWidth I) (targetInput I)))
        I.targetPoint.toMathlib := by
  obtain ⟨base, target⟩ :=
    ecdlpRecovery_prefix_points I A initial admitted prefixCode record positive
  rw [base, target]
  exact ⟨encodePoint_represents (curve E) I.basePoint.toMathlib,
    encodePoint_represents (curve E) I.targetPoint.toMathlib⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical.QueryModel.Recovery
