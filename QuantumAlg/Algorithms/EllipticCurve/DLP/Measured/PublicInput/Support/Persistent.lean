/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Support.Points
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent
import all QuantumAlg.Core.Execution.CycleSchedule.InputDistribution

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

/-- Carry the uniquely empty service state and original store through persistent recovery. -/
def persistentInitialState (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : Input (Allocation.before p.size (2 * exponentWidth)) Reference) :
    State (before E exponentWidth) Reference (Unit × Store (before E exponentWidth)) :=
  (initialInput E exponentWidth problem original).state.mapClassical
    (fun value => (value, ((), value)))

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

/-- The two public-point reads depend only on the borrowed classical value,
even when the seven persistent cells and measured sample differ. -/
theorem persistent_publicPointReads_eq_of_borrowed
    (first second : Store (persistentCtx (terminal E exponentWidth)
      (Canonical.Layout.fieldWidth E) exponentWidth))
    (same : first.readBorrowedClassical = second.readBorrowedClassical) :
    first.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
      (terminalBaseRef E exponentWidth)) =
        second.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
          (terminalBaseRef E exponentWidth)) ∧
    first.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
      (terminalTargetRef E exponentWidth)) =
        second.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
          (terminalTargetRef E exponentWidth)) := by
  let width := Canonical.Layout.fieldWidth E
  let firstTail := persistentTail width exponentWidth first
  let secondTail := persistentTail width exponentWidth second
  have sameTail : HEq firstTail.readBorrowedClassical secondTail.readBorrowedClassical :=
    (persistentTail_borrowed width exponentWidth first).symm.trans
      ((heq_of_eq same).trans (persistentTail_borrowed width exponentWidth second))
  have firstFrame := readBorrowedClassical_split_right (terminal_disjoint E exponentWidth)
    (original_terminal_noBorrowedClassical (p := p) exponentWidth) firstTail
  have secondFrame := readBorrowedClassical_split_right (terminal_disjoint E exponentWidth)
    (original_terminal_noBorrowedClassical (p := p) exponentWidth) secondTail
  have frameEq :
      (split (terminal_disjoint E exponentWidth) firstTail).2 =
        (split (terminal_disjoint E exponentWidth) secondTail).2 :=
    frame_store_eq_of_borrowed_eq E exponentWidth _ _
      (eq_of_heq (firstFrame.symm.trans (sameTail.trans secondFrame)))
  have baseRead (value : Store (persistentCtx (terminal E exponentWidth)
      width exponentWidth)) :
      value.read (persistentInput width exponentWidth (terminalBaseRef E exponentWidth)) =
        (split (terminal_disjoint E exponentWidth)
          (persistentTail width exponentWidth value)).2.read (baseRef E exponentWidth) := by
    let tail := persistentTail width exponentWidth value
    have joined := join_split_store (terminal_disjoint E exponentWidth) tail
    have actual := congrArg (fun result : Store (terminal E exponentWidth) =>
      result.read (terminalBaseRef E exponentWidth)) joined
    have base := contextUnion_read_join_right (terminal_disjoint E exponentWidth)
      (split (terminal_disjoint E exponentWidth) tail).1
      (split (terminal_disjoint E exponentWidth) tail).2 (baseRef E exponentWidth)
    exact (persistentTail_read width exponentWidth value
      (terminalBaseRef E exponentWidth)).symm.trans (actual.symm.trans base)
  have targetRead (value : Store (persistentCtx (terminal E exponentWidth)
      width exponentWidth)) :
      value.read (persistentInput width exponentWidth (terminalTargetRef E exponentWidth)) =
        (split (terminal_disjoint E exponentWidth)
          (persistentTail width exponentWidth value)).2.read (targetRef E exponentWidth) := by
    let tail := persistentTail width exponentWidth value
    have joined := join_split_store (terminal_disjoint E exponentWidth) tail
    have actual := congrArg (fun result : Store (terminal E exponentWidth) =>
      result.read (terminalTargetRef E exponentWidth)) joined
    have target := contextUnion_read_join_right (terminal_disjoint E exponentWidth)
      (split (terminal_disjoint E exponentWidth) tail).1
      (split (terminal_disjoint E exponentWidth) tail).2 (targetRef E exponentWidth)
    exact (persistentTail_read width exponentWidth value
      (terminalTargetRef E exponentWidth)).symm.trans (actual.symm.trans target)
  constructor
  · calc
      _ = (split (terminal_disjoint E exponentWidth) firstTail).2.read
          (baseRef E exponentWidth) := baseRead first
      _ = (split (terminal_disjoint E exponentWidth) secondTail).2.read
          (baseRef E exponentWidth) := congrArg (fun store => store.read
            (baseRef E exponentWidth)) frameEq
      _ = _ := (baseRead second).symm
  · calc
      _ = (split (terminal_disjoint E exponentWidth) firstTail).2.read
          (targetRef E exponentWidth) := targetRead first
      _ = (split (terminal_disjoint E exponentWidth) secondTail).2.read
          (targetRef E exponentWidth) := congrArg (fun store => store.read
            (targetRef E exponentWidth)) frameEq
      _ = _ := (targetRead second).symm

/-- A supported output of any real persistent program retains both public-point
reads of one supported input block, even with arbitrary quantum references. -/
theorem persistentProgram_supported_publicPointReads
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E) exponentWidth)
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E) exponentWidth))
    (noQuantum :
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E)
        exponentWidth).borrowedQuantumWires = [])
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (terminal E exponentWidth)
      (Canonical.Layout.fieldWidth E) exponentWidth) Reference (Unit × H))
    (result : Store (persistentCtx (terminal E exponentWidth)
      (Canonical.Layout.fieldWidth E) exponentWidth) × (Unit × (H × code.Path)))
    (positive : 0 < ((code.execute Reference state).block result).mass) :
    ∃ previous : Store (persistentCtx (terminal E exponentWidth)
        (Canonical.Layout.fieldWidth E) exponentWidth) × (Unit × H),
      0 < (state.block previous).mass ∧
      previous.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalBaseRef E exponentWidth)) =
        result.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
          (terminalBaseRef E exponentWidth)) ∧
      previous.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalTargetRef E exponentWidth)) =
        result.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
          (terminalTargetRef E exponentWidth)) := by
  have restored := code.borrowedRestored_of_noBorrowedQuantum noQuantum Reference state
  obtain ⟨previous, present, same⟩ := code.borrowedRestored_supported_initial
    Reference state _ restored result positive
  have sameValue : previous.1.readBorrowedClassical =
      result.1.readBorrowedClassical :=
    same.trans (eq_of_heq (borrowed_transport_heq code result.1.readBorrowedClassical))
  obtain ⟨baseEq, targetEq⟩ :=
    persistent_publicPointReads_eq_of_borrowed E exponentWidth previous.1 result.1 sameValue
  exact ⟨previous, present, baseEq, targetEq⟩

/-- At an actual cycle boundary, forgetting execution paths retains the two
public-point reads from a supported entered block of the same input. -/
theorem persistentProgram_nextInput_publicPointReads
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E) exponentWidth)
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E) exponentWidth))
    (noQuantum :
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E)
        exponentWidth).borrowedQuantumWires = [])
    {Reference : Register}
    (input : OracleInput .empty
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E)
        exponentWidth) Reference)
    (record : Store (persistentCtx (terminal E exponentWidth)
      (Canonical.Layout.fieldWidth E) exponentWidth) ×
      ClassicalOracleModel.empty.HiddenState)
    (positive : 0 < ((code.nextInput input).localState.block record).mass) :
    ∃ previous : Store (persistentCtx (terminal E exponentWidth)
        (Canonical.Layout.fieldWidth E) exponentWidth) × (Unit × Unit),
      0 < ((input.state.mapClassical
        (fun value => (value.1, (value.2, ())))).block previous).mass ∧
      previous.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalBaseRef E exponentWidth)) =
        record.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
          (terminalBaseRef E exponentWidth)) ∧
      previous.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalTargetRef E exponentWidth)) =
        record.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
          (terminalTargetRef E exponentWidth)) := by
  obtain ⟨result, sameStore, _, supported⟩ :=
    Circuit.nextInput_local_supported_execution code input record positive
  have restored := code.borrowedRestored_of_noBorrowedQuantum noQuantum Reference
    (input.state.mapClassical (fun value => (value.1, (value.2, ()))))
  obtain ⟨previous, present, same⟩ := code.borrowedRestored_supported_initial
    Reference (input.state.mapClassical (fun value => (value.1, (value.2, ()))))
    _ restored result supported
  have sameValue : previous.1.readBorrowedClassical =
      result.1.readBorrowedClassical :=
    same.trans (eq_of_heq (borrowed_transport_heq code result.1.readBorrowedClassical))
  obtain ⟨baseEq, targetEq⟩ :=
    persistent_publicPointReads_eq_of_borrowed E exponentWidth previous.1 result.1 sameValue
  exact ⟨previous, present,
    baseEq.trans (congrArg (fun store => store.read
      (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalBaseRef E exponentWidth))) sameStore),
    targetEq.trans (congrArg (fun store => store.read
      (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalTargetRef E exponentWidth))) sameStore)⟩

/-- Any real circuit on the persistent terminal context carries valid public
point representations from its supported input blocks to its output blocks.
Only the borrowed interface is used; retained cells and quantum references
may be arbitrary. -/
theorem persistentProgram_preserves_represents
    (problem : KnownOrderProblem E.GroupPoint)
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E) exponentWidth)
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E) exponentWidth))
    (noQuantum :
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E)
        exponentWidth).borrowedQuantumWires = [])
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx (terminal E exponentWidth)
      (Canonical.Layout.fieldWidth E) exponentWidth) Reference (Unit × H))
    (holds : ∀ entry, 0 < (state.block entry).mass →
      ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
          (terminalBaseRef E exponentWidth))) problem.generator.toMathlib ∧
      ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
          (terminalTargetRef E exponentWidth))) problem.target.toMathlib)
    (result : Store (persistentCtx (terminal E exponentWidth)
      (Canonical.Layout.fieldWidth E) exponentWidth) × (Unit × (H × code.Path)))
    (positive : 0 < ((code.execute Reference state).block result).mass) :
    ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
      (result.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalBaseRef E exponentWidth))) problem.generator.toMathlib ∧
    ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
      (result.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalTargetRef E exponentWidth))) problem.target.toMathlib := by
  have restored := code.borrowedRestored_of_noBorrowedQuantum noQuantum Reference state
  obtain ⟨previous, present, same⟩ := code.borrowedRestored_supported_initial
    Reference state _ restored result positive
  have sameValue : previous.1.readBorrowedClassical =
      result.1.readBorrowedClassical :=
    same.trans (eq_of_heq (borrowed_transport_heq code result.1.readBorrowedClassical))
  obtain ⟨baseEq, targetEq⟩ :=
    persistent_publicPointReads_eq_of_borrowed E exponentWidth previous.1 result.1 sameValue
  obtain ⟨baseValid, targetValid⟩ := holds previous present
  constructor
  · rw [← baseEq]
    exact baseValid
  · rw [← targetEq]
    exact targetValid

/-- Every positive actual persistent record retains the original prescribed borrowed points. -/
theorem persistentProgram_supported_points (problem : KnownOrderProblem E.GroupPoint)
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model) (before E exponentWidth)
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E) exponentWidth))
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * exponentWidth)) Reference)
    (record : Store (persistentCtx (terminal E exponentWidth)
      (Canonical.Layout.fieldWidth E) exponentWidth) ×
        (Unit × (Store (before E exponentWidth) × code.Path)))
    (positive : 0 < ((code.execute Reference
      (persistentInitialState E exponentWidth problem original)).block record).mass) :
    record.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalBaseRef E exponentWidth)) =
        Canonical.Runtime.Context.pointValue E problem.generator.toMathlib ∧
      record.1.read (persistentInput (Canonical.Layout.fieldWidth E) exponentWidth
        (terminalTargetRef E exponentWidth)) =
        Canonical.Runtime.Context.pointValue E problem.target.toMathlib := by
  let initial := persistentInitialState E exponentWidth problem original
  have restored := code.borrowedRestored_of_noBorrowedQuantum
    (before_noBorrowedQuantum E exponentWidth) Reference initial
  obtain ⟨previous, previousPositive, same⟩ := code.borrowedRestored_supported_initial
    Reference initial _ restored record positive
  obtain ⟨value, rfl, valuePositive⟩ := (ExecutionState.mapClassical_block_mass_pos_iff
    (initialInput E exponentWidth problem original).state
      (fun value => (value, ((), value))) previous).mp
      (by
        apply lt_of_lt_of_eq previousPositive
        simp only [initial, persistentInitialState, ExecutionState.mapClassical_block_mass])
  obtain ⟨source, constructed, _sourcePositive⟩ := initialState_supported_original E exponentWidth
    problem original.state value valuePositive
  apply persistent_points_of_borrowed E exponentWidth problem source record.1
  exact (heq_of_eq (congrArg Store.readBorrowedClassical constructed)).trans
    ((heq_of_eq same).trans (borrowed_transport_heq code record.1.readBorrowedClassical))

/-- Actual public-point interpretations need no additional caller support condition. -/
theorem persistentProgram_supported_represents (problem : KnownOrderProblem E.GroupPoint)
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model) (before E exponentWidth)
      (persistentCtx (terminal E exponentWidth) (Canonical.Layout.fieldWidth E) exponentWidth))
    {Reference : Register}
    (original : Input (Allocation.before p.size (2 * exponentWidth)) Reference)
    (record : Store (persistentCtx (terminal E exponentWidth)
      (Canonical.Layout.fieldWidth E) exponentWidth) ×
        (Unit × (Store (before E exponentWidth) × code.Path)))
    (positive : 0 < ((code.execute Reference
      (persistentInitialState E exponentWidth problem original)).block record).mass) :
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
