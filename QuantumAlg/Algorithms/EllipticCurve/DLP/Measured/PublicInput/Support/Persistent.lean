/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Points
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent

/-!
# Prescribed public points throughout actual persistent recovery

Every actual circuit from the prescribed input to the existing persistent
terminal context preserves the original borrowed public values. Positive
output blocks therefore carry the original point interpretations internally.
The seven retained cells are only projected in proof coordinates; no initial
value, inverse, selected candidate or public-point promise is added.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def persistentTail {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width scalarWidth : Nat) (value : Store (persistentCtx ctx width scalarWidth)) : Store ctx :=
  ⟨value.cells.2.2.2.2.2.2.2⟩

private theorem retainedTail_read {kind : ProblemKind} {ctx : RuntimeCtx kind}
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

private theorem persistentTail_read {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width scalarWidth : Nat) (value : Store (persistentCtx ctx width scalarWidth))
    {shape : CShape} (input : CInputRef ctx shape) :
    (persistentTail width scalarWidth value).read input =
      value.read (persistentInput width scalarWidth input) := by
  unfold persistentInput retainedInput
  erw [← retainedTail_read, ← retainedTail_read, ← retainedTail_read,
    ← retainedTail_read, ← retainedTail_read, ← retainedTail_read, ← retainedTail_read]
  rfl

private theorem persistentTail_borrowed {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width scalarWidth : Nat) (value : Store (persistentCtx ctx width scalarWidth)) :
    HEq value.readBorrowedClassical
      (persistentTail width scalarWidth value).readBorrowedClassical := by
  rfl

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

private theorem persistent_points_of_borrowed (problem : KnownOrderProblem E.GroupPoint)
    (source : Store (Allocation.before p.size (2 * exponentWidth)))
    (value : Store (persistentCtx (terminal E exponentWidth)
      (Canonical.Layout.fieldWidth E) exponentWidth))
    (same : HEq (initialStore E exponentWidth problem source).readBorrowedClassical
      value.readBorrowedClassical) :
    value.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalBaseRef E exponentWidth)) =
        Canonical.Runtime.Context.pointValue E problem.generator.toMathlib ∧
      value.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalTargetRef E exponentWidth)) =
        Canonical.Runtime.Context.pointValue E problem.target.toMathlib := by
  let tail := persistentTail (Canonical.Layout.fieldWidth E) exponentWidth value
  have initialBorrowed := readBorrowedClassical_join_right (before_disjoint E exponentWidth)
    (original_before_noBorrowedClassical (p := p) exponentWidth)
    source (store E exponentWidth problem)
  have finalBorrowed := readBorrowedClassical_split_right (terminal_disjoint E exponentWidth)
    (original_terminal_noBorrowedClassical (p := p) exponentWidth) tail
  have frames := initialBorrowed.symm.trans
    (same.trans ((persistentTail_borrowed (Canonical.Layout.fieldWidth E) exponentWidth value).trans
      finalBorrowed))
  have equalFrame := (frame_store_eq_of_borrowed_eq E exponentWidth
    (store E exponentWidth problem) (split (terminal_disjoint E exponentWidth) tail).2
    (eq_of_heq frames)).symm
  have baseRead := contextUnion_read_join_right (terminal_disjoint E exponentWidth)
    (split (terminal_disjoint E exponentWidth) tail).1
    (split (terminal_disjoint E exponentWidth) tail).2 (baseRef E exponentWidth)
  have targetRead := contextUnion_read_join_right (terminal_disjoint E exponentWidth)
    (split (terminal_disjoint E exponentWidth) tail).1
    (split (terminal_disjoint E exponentWidth) tail).2 (targetRef E exponentWidth)
  have joined := join_split_store (terminal_disjoint E exponentWidth) tail
  have actualBase := congrArg (fun result : Store (terminal E exponentWidth) =>
    result.read (terminalBaseRef E exponentWidth)) joined
  have actualTarget := congrArg (fun result : Store (terminal E exponentWidth) =>
    result.read (terminalTargetRef E exponentWidth)) joined
  have prescribedBase := congrArg (fun result : Store (frame E exponentWidth) =>
    result.read (baseRef E exponentWidth)) equalFrame
  have prescribedTarget := congrArg (fun result : Store (frame E exponentWidth) =>
    result.read (targetRef E exponentWidth)) equalFrame
  have terminalBase := actualBase.symm.trans (baseRead.trans
    (prescribedBase.trans (store_base E exponentWidth problem)))
  have terminalTarget := actualTarget.symm.trans (targetRead.trans
    (prescribedTarget.trans (store_target E exponentWidth problem)))
  exact ⟨(persistentTail_read (Canonical.Layout.fieldWidth E) exponentWidth value
      (terminalBaseRef E exponentWidth)).symm.trans terminalBase,
    (persistentTail_read (Canonical.Layout.fieldWidth E) exponentWidth value
      (terminalTargetRef E exponentWidth)).symm.trans terminalTarget⟩

/-- Every positive actual persistent record retains the original prescribed borrowed points. -/
theorem persistentProgram_supported_points (problem : KnownOrderProblem E.GroupPoint)
    (code : Circuit (before E exponentWidth)
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E) exponentWidth))
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * exponentWidth)) Reference)
    (record : Store (persistentCtx (terminal E exponentWidth)
      (Canonical.Layout.fieldWidth E) exponentWidth) ×
        (Store (before E exponentWidth) × code.Path))
    (positive : 0 < ((code.execute Reference
      ((initialInput E exponentWidth problem original).state.mapClassical
        (fun value => (value, value)))).block record).mass) :
    record.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalBaseRef E exponentWidth)) =
        Canonical.Runtime.Context.pointValue E problem.generator.toMathlib ∧
      record.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalTargetRef E exponentWidth)) =
        Canonical.Runtime.Context.pointValue E problem.target.toMathlib := by
  let initial := (initialInput E exponentWidth problem original).state.mapClassical
    (fun value => (value, value))
  have restored := code.borrowedRestored_of_noBorrowedQuantum
    (before_noBorrowedQuantum E exponentWidth) Reference initial
  obtain ⟨previous, previousPositive, same⟩ := code.borrowedRestored_supported_initial
    Reference initial _ restored record positive
  obtain ⟨value, rfl, valuePositive⟩ := (ExecutionState.mapClassical_block_mass_pos_iff
    (initialInput E exponentWidth problem original).state (fun value => (value, value)) previous).mp
      (by
        apply lt_of_lt_of_eq previousPositive
        simp only [initial, ExecutionState.mapClassical_block_mass]
        apply Finset.sum_congr rfl
        intro source _
        split_ifs <;> rfl)
  obtain ⟨source, constructed, _sourcePositive⟩ := initialState_supported_original E exponentWidth
    problem original.state value valuePositive
  apply persistent_points_of_borrowed E exponentWidth problem source record.1
  exact (heq_of_eq (congrArg Store.readBorrowedClassical constructed)).trans
    ((heq_of_eq same).trans (borrowed_transport_heq code record.1.readBorrowedClassical))

/-- Actual public-point interpretations need no additional caller support condition. -/
theorem persistentProgram_supported_represents (problem : KnownOrderProblem E.GroupPoint)
    (code : Circuit (before E exponentWidth)
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E) exponentWidth))
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * exponentWidth)) Reference)
    (record : Store (persistentCtx (terminal E exponentWidth)
      (Canonical.Layout.fieldWidth E) exponentWidth) ×
        (Store (before E exponentWidth) × code.Path))
    (positive : 0 < ((code.execute Reference
      ((initialInput E exponentWidth problem original).state.mapClassical
        (fun value => (value, value)))).block record).mass) :
    ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
        (record.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
          (terminalBaseRef E exponentWidth))) problem.generator.toMathlib ∧
      ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
        (record.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
          (terminalTargetRef E exponentWidth))) problem.target.toMathlib := by
  obtain ⟨baseValue, targetValue⟩ :=
    persistentProgram_supported_points E exponentWidth problem code original record positive
  rw [baseValue, targetValue]
  exact ⟨publicPoint_represents E problem.generator, publicPoint_represents E problem.target⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput
