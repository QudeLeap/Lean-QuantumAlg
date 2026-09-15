/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Runtime.Context.Input
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Recovery
import all QuantumAlg.Core.Execution.Borrowed.Support
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Components.Classical.EllipticCurve.Representation.Model

/-!
# Original borrowed public points throughout actual native recovery

The original two input values are admitted at the original input boundary.
Every actual prefix preserves their complete borrowed observation. Projecting
classical cells only in the proof identifies the same original structural
reads below the owned bank, finite measurements and seven recovery cells.
Every positive execution block therefore represents the original public
points, including infinity, without an intermediate input promise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native.PublicInput

open Execution ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

/-- The original caller supplies two classical public points and no quantum bank. -/
theorem nativeECDLP_input_quantumWires (I : ECDLPInstance E) :
    (Runtime.Context.pre I).quantumWires = [] := rfl

/-- The complete borrowed public interface contains no quantum wire. -/
theorem nativeECDLP_input_noBorrowedQuantum (I : ECDLPInstance E) :
    (Runtime.Context.pre I).borrowedQuantumWires = [] := rfl

private theorem retained_read {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys)
    (value : Store (ctx.addRetained key shape fresh)) {inputShape : CShape}
    (input : CInputRef ctx inputShape) :
    (Store.mk value.cells.2).read input = value.read (input.underRetained key shape fresh) := by
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

private def cellsTail {kind : ProblemKind} {ctx : RuntimeCtx kind} (dimension : ℕ+) :
    (count : Nat) → Store (MeasurementCells.context ctx dimension count) → Store ctx
  | 0, value => value
  | count + 1, value => cellsTail dimension count ⟨value.cells.2⟩

private theorem cellsTail_read {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (dimension : ℕ+) (count : Nat)
    (value : Store (MeasurementCells.context ctx dimension count)) {shape : CShape}
    (input : CInputRef ctx shape) :
    (cellsTail dimension count value).read input =
      value.read (MeasurementCells.liftInput dimension input count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact (ih ⟨value.cells.2⟩).trans (retained_read _ _ _ value _)

private theorem cellsTail_borrowed {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (dimension : ℕ+) (count : Nat)
    (value : Store (MeasurementCells.context ctx dimension count)) :
    HEq value.readBorrowedClassical (cellsTail dimension count value).readBorrowedClassical := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih ⟨value.cells.2⟩

variable (I : ECDLPInstance E)

private def originalStore
    (value : Store (context (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I)) :
    Store (Runtime.Context.pre I) :=
  ⟨(cellsTail 2 (sampleWidth I) value).cells.2⟩

private theorem originalStore_read
    (value : Store (context (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I))
    {shape : CShape} (input : CInputRef (Runtime.Context.pre I) shape) :
    (originalStore I value).read input =
      value.read
        (liftInput (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I input) := by
  let bank := cellsTail 2 (sampleWidth I) value
  have same : (originalStore I value).pushOwnedLayout
      (Runtime.Context.pre I).canonicalFreshKey (bankLayout I)
      (Runtime.Context.pre I).canonicalFreshKey_fresh
      (allocationDisjoint (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I) = bank := by
    change (Store.mk bank.cells.2).pushOwnedLayout _ _ _ _ = bank
    obtain ⟨⟨marker, rest⟩⟩ := bank
    cases marker
    rfl
  have read := Store.read_pushOwnedLayout_underOwnedLayout (originalStore I value)
    (Runtime.Context.pre I).canonicalFreshKey (bankLayout I)
    (Runtime.Context.pre I).canonicalFreshKey_fresh
    (allocationDisjoint (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I) input
  rw [same] at read
  exact read.symm.trans (cellsTail_read 2 (sampleWidth I) value _)

private theorem originalStore_borrowed
    (value : Store (context (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I)) :
    HEq value.readBorrowedClassical (originalStore I value).readBorrowedClassical :=
  cellsTail_borrowed 2 (sampleWidth I) value

private def persistentTail {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width scalarWidth : Nat) (value : Store (persistentCtx ctx width scalarWidth)) : Store ctx :=
  ⟨value.cells.2.2.2.2.2.2.2⟩

private theorem persistentTail_read {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width scalarWidth : Nat) (value : Store (persistentCtx ctx width scalarWidth))
    {shape : CShape} (input : CInputRef ctx shape) :
    (persistentTail width scalarWidth value).read input =
      value.read (persistentInput width scalarWidth input) := by
  unfold persistentInput retainedInput
  erw [← retained_read, ← retained_read, ← retained_read, ← retained_read,
    ← retained_read, ← retained_read, ← retained_read]
  rfl

private theorem input_store_eq_of_borrowed
    (first second : Store (Runtime.Context.pre I))
    (same : first.readBorrowedClassical = second.readBorrowedClassical) : first = second := by
  obtain ⟨first⟩ := first
  obtain ⟨second⟩ := second
  obtain ⟨firstTarget, firstBase, firstUnit⟩ := first
  obtain ⟨secondTarget, secondBase, secondUnit⟩ := second
  cases firstUnit
  cases secondUnit
  change CShape.Value.product firstTarget (.product firstBase .unit) =
    CShape.Value.product secondTarget (.product secondBase .unit) at same
  cases same
  rfl

private theorem borrowed_transport_heq {kind : ProblemKind} {pre post : RuntimeCtx kind}
    (code : Circuit pre post) (value : post.borrowedClassicalShape.Value) :
    HEq (code.borrowedClassicalValueTransport value) value :=
  ((Equiv.cast_eq_iff_heq
    (congrArg CShape.Value code.borrowedClassicalShape_preserved)).mp rfl).symm

/-- Every actual persistent prefix retains both prescribed original public points. -/
theorem nativeECDLP_persistent_supported_points
    (code : Circuit (Runtime.Context.pre I)
      (persistentCtx (context (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I)
        (Layout.fieldWidth E) (FiniteCyclicDLP.orderWidth (problem I))))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (Runtime.Context.pre I) Reference H)
    (valid : ∀ entry, 0 < (state.block entry).mass → entry.1 = Runtime.Context.inputStore I)
    (record : Store _ × (H × code.Path))
    (positive : 0 < ((code.execute Reference state).block record).mass) :
    record.1.read (persistentInput (Layout.fieldWidth E) (FiniteCyclicDLP.orderWidth (problem I))
      (liftInput (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I
        (Runtime.Context.baseRef I))) = Runtime.Context.baseValue I ∧
    record.1.read (persistentInput (Layout.fieldWidth E) (FiniteCyclicDLP.orderWidth (problem I))
      (liftInput (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I
        (Runtime.Context.targetRef I))) = Runtime.Context.targetValue I := by
  have restored := code.borrowedRestored_of_noBorrowedQuantum
    (nativeECDLP_input_noBorrowedQuantum I) Reference state
  obtain ⟨previous, present, same⟩ :=
    code.borrowedRestored_supported_initial Reference state _ restored record positive
  let tail := persistentTail (Layout.fieldWidth E)
    (FiniteCyclicDLP.orderWidth (problem I)) record.1
  have finalBorrowed : HEq record.1.readBorrowedClassical
      (originalStore I tail).readBorrowedClassical := originalStore_borrowed I tail
  have frames := (heq_of_eq same).trans
    ((borrowed_transport_heq code record.1.readBorrowedClassical).trans finalBorrowed)
  have equalStore := input_store_eq_of_borrowed I previous.1
    (originalStore I tail) (eq_of_heq frames)
  have prescribed : originalStore I tail = Runtime.Context.inputStore I :=
    equalStore.symm.trans (valid previous present)
  constructor
  · exact (persistentTail_read _ _ record.1 _).symm.trans
      ((originalStore_read I tail _).symm.trans
        ((congrArg (fun value => value.read (Runtime.Context.baseRef I)) prescribed).trans
          (Runtime.Context.inputStore_base I)))
  · exact (persistentTail_read _ _ record.1 _).symm.trans
      ((originalStore_read I tail _).symm.trans
        ((congrArg (fun value => value.read (Runtime.Context.targetRef I)) prescribed).trans
          (Runtime.Context.inputStore_target I)))

/-- Positive actual prefixes meet the original complete point interpretation internally. -/
theorem nativeECDLP_persistent_supported_represents
    (code : Circuit (Runtime.Context.pre I)
      (persistentCtx (context (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I)
        (Layout.fieldWidth E) (FiniteCyclicDLP.orderWidth (problem I))))
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (Runtime.Context.pre I) Reference H)
    (valid : ∀ entry, 0 < (state.block entry).mass → entry.1 = Runtime.Context.inputStore I)
    (record : Store _ × (H × code.Path))
    (positive : 0 < ((code.execute Reference state).block record).mass) :
    ClassicalRoutines.EllipticCurve.PointRepresents (Layout.curveSpec E)
      (record.1.read (persistentInput (Layout.fieldWidth E)
        (FiniteCyclicDLP.orderWidth (problem I))
        (liftInput (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I
          (Runtime.Context.baseRef I)))) I.basePoint.toMathlib ∧
    ClassicalRoutines.EllipticCurve.PointRepresents (Layout.curveSpec E)
      (record.1.read (persistentInput (Layout.fieldWidth E)
        (FiniteCyclicDLP.orderWidth (problem I))
        (liftInput (Runtime.Context.pre I) (nativeECDLP_input_quantumWires I) I
          (Runtime.Context.targetRef I)))) I.targetPoint.toMathlib := by
  obtain ⟨baseValue, targetValue⟩ :=
    nativeECDLP_persistent_supported_points I code state valid record positive
  rw [baseValue, targetValue]
  exact ⟨ClassicalRoutines.EllipticCurve.encodePoint_represents (Layout.curveSpec E) _,
    ClassicalRoutines.EllipticCurve.encodePoint_represents (Layout.curveSpec E) _⟩

end

end GateLevelAttempt.Native.PublicInput
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
