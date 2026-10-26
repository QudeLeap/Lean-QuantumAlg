/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Domain
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Probability
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Points
import all QuantumAlg.Core.Execution.Borrowed.Classical.Read
import all QuantumAlg.Core.Execution.Measurement.Cells.Borrowed

/-!
# The original public point domain at every actual streaming recovery prefix

Only the two identity-inclusive public point values are prescribed before
execution. The input encoder emits no circuit instruction and retains the
complete quantum marginal with arbitrary external Reference. Every input in
the independent local point-value domain is already this prescribed input.

The actual run still performs its physical bank allocation, every reset,
seven-cell retention and checked attempt. Borrowed restoration supplies both
point interpretations on every positive block of every actual prefix. No
caller point-representation, clean-bank or initialized-latch certificate is
required.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
namespace Support

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.Execution.ContextUnion
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP Canonical.Probability
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat)

private lemma frame_store_eq (problem : KnownOrderProblem E.GroupPoint)
    (stored : Store (Recovery.PublicInput.frame E m))
    (base : stored.read (Recovery.PublicInput.baseRef E m) =
      ECDLP.Canonical.Runtime.Context.pointValue E problem.generator.toMathlib)
    (target : stored.read (Recovery.PublicInput.targetRef E m) =
      ECDLP.Canonical.Runtime.Context.pointValue E problem.target.toMathlib) :
    stored = Recovery.PublicInput.store E m problem.generator.toMathlib
      problem.target.toMathlib := by
  obtain ⟨targetValue, baseValue, rest⟩ := stored
  cases rest
  change baseValue = _ at base
  change targetValue = _ at target
  subst baseValue
  subst targetValue
  rfl

/-- Supplying the original public problem changes only its classical input encoding. -/
def prescribedInput (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E m) Reference) :
    Input (Recovery.PublicInput.frame E m) Reference where
  state := original.state.mapClassical
    (fun _ => Recovery.PublicInput.store E m problem.generator.toMathlib problem.target.toMathlib)
  normalized := (original.state.mapClassical_mass _).trans original.normalized

/-- Every full quantum-reference coherence of the input marginal is retained. -/
lemma prescribedInput_quantumMarginal (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register} (original : Input (Recovery.PublicInput.frame E m) Reference) :
    (prescribedInput E m problem original).state.quantumMarginal =
      original.state.quantumMarginal := ExecutionState.mapClassical_quantumMarginal _ _

private lemma input_eq_of_state_eq {ctx : RuntimeCtx .quantum} {Reference : Register}
    (first second : Input ctx Reference) (same : first.state = second.state) : first = second := by
  cases first
  cases second
  cases same
  rfl

/-- Encoding an already admissible input preserves its entire state, including Reference. -/
lemma prescribedInput_eq_of_domain (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register} (original : Input (Recovery.PublicInput.frame E m) Reference)
    (valid : inputDomain E m problem original.localState) :
    prescribedInput E m problem original = original := by
  apply input_eq_of_state_eq
  refine (ExecutionState.mapClassical_eq_of_support original.state _ id ?_).trans
    (ExecutionState.mapClassical_id original.state)
  intro stored positive
  have values := valid stored ((original.localState_block_mass stored).symm ▸ positive)
  exact (frame_store_eq E m problem stored values.1 values.2).symm

/-- The prescribed input is in the same independent local point-value domain. -/
lemma inputDomain_prescribedInput (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register} (original : Input (Recovery.PublicInput.frame E m) Reference) :
    inputDomain E m problem (prescribedInput E m problem original).localState := by
  intro stored positive
  rw [Input.localState_block_mass] at positive
  obtain ⟨source, same, _⟩ := (ExecutionState.mapClassical_block_mass_pos_iff original.state
    (fun _ => Recovery.PublicInput.store E m problem.generator.toMathlib problem.target.toMathlib)
    stored).mp positive
  rw [← same]
  exact ⟨Recovery.PublicInput.store_base E m _ _, Recovery.PublicInput.store_target E m _ _⟩

/-- Attach the uniquely empty service state without changing the actual supplied Store. -/
def oracleInput (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E m) Reference) :
    OracleInput .empty (Recovery.PublicInput.frame E m) Reference where
  state := (prescribedInput E m problem original).state.mapClassical (fun stored => (stored, ()))
  normalized := ((prescribedInput E m problem original).state.mapClassical_mass _).trans
    (prescribedInput E m problem original).normalized

/-- Record the real original Store in the actual circuit's input History. -/
def enteredState (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E m) Reference) :
    State (Recovery.PublicInput.frame E m) Reference (Unit × Store (Recovery.PublicInput.frame E
      m)) :=
  (oracleInput E m problem original).state.mapClassical
    (fun record => (record.1, (record.2, record.1)))

lemma enteredState_mass (problem : KnownOrderProblem E.GroupPoint) {Reference : Register}
    (original : Input (Recovery.PublicInput.frame E m) Reference) :
    (enteredState E m problem original).mass = 1 := by
  unfold enteredState
  exact ((oracleInput E m problem original).state.mapClassical_mass _).trans
    (oracleInput E m problem original).normalized

include E in
private lemma terminal_noBorrowedClassical :
    (Recovery.Layout.terminal p.size m).borrowedClassicalCells = [] := by
  have preserved := (Recovery.PublicInput.Allocation.circuit E m).borrowedClassicalCells_preserved
  change ((Recovery.Layout.terminal p.size m).entries ++ (Recovery.PublicInput.frame E
    m).entries).flatMap
    RuntimeEntry.borrowedClassicalCells =
      (Recovery.PublicInput.frame E m).borrowedClassicalCells at preserved
  rw [List.flatMap_append] at preserved
  change (Recovery.Layout.terminal p.size m).borrowedClassicalCells ++
    (Recovery.PublicInput.frame E m).borrowedClassicalCells =
      (Recovery.PublicInput.frame E m).borrowedClassicalCells at preserved
  have lengths := congrArg List.length preserved
  rw [List.length_append] at lengths
  exact List.eq_nil_of_length_eq_zero (by omega)

private def persistentTail {ctx : RuntimeCtx .quantum} (width scalarWidth : Nat)
    (stored : Store (persistentCtx ctx width scalarWidth)) : Store ctx :=
  ⟨stored.cells.2.2.2.2.2.2.2⟩

private lemma persistentTail_read {ctx : RuntimeCtx .quantum} (width scalarWidth : Nat)
    (stored : Store (persistentCtx ctx width scalarWidth)) {shape : CShape}
    (input : CInputRef ctx shape) :
    (persistentTail width scalarWidth stored).read input =
      stored.read (persistentInput width scalarWidth input) := by
  unfold persistentInput retainedInput
  erw [← Store.retainedTail_read, ← Store.retainedTail_read, ← Store.retainedTail_read,
    ← Store.retainedTail_read, ← Store.retainedTail_read, ← Store.retainedTail_read,
    ← Store.retainedTail_read]
  rfl

private lemma persistentTail_borrowed {ctx : RuntimeCtx .quantum} (width scalarWidth : Nat)
    (stored : Store (persistentCtx ctx width scalarWidth)) :
    HEq stored.readBorrowedClassical
      (persistentTail width scalarWidth stored).readBorrowedClassical := by
  rfl

private lemma borrowed_transport_heq {origin final : RuntimeCtx .quantum}
    (code : Circuit Model origin final) (value : final.borrowedClassicalShape.Value) :
    HEq (code.borrowedClassicalValueTransport value) value := by
  exact ((Equiv.cast_eq_iff_heq
    (congrArg CShape.Value code.borrowedClassicalShape_preserved)).mp rfl).symm

variable (problem : KnownOrderProblem E.GroupPoint)

set_option maxHeartbeats 400000 in
-- Reading both original point values through the complete borrowed Store needs a local budget.
private lemma persistent_points_of_borrowed
    (stored : Store (persistentCtx (Recovery.PublicInput.context E m)
      (ECDLP.Canonical.Layout.fieldWidth E) m))
    (same : HEq (Recovery.PublicInput.store E m problem.generator.toMathlib
      problem.target.toMathlib).readBorrowedClassical stored.readBorrowedClassical) :
    stored.read (persistentInput (ECDLP.Canonical.Layout.fieldWidth E) m
      (Recovery.PublicInput.contextBaseRef E m)) =
        ECDLP.Canonical.Runtime.Context.pointValue E problem.generator.toMathlib ∧
      stored.read (persistentInput (ECDLP.Canonical.Layout.fieldWidth E) m
        (Recovery.PublicInput.contextTargetRef E m)) =
        ECDLP.Canonical.Runtime.Context.pointValue E problem.target.toMathlib := by
  let tail := persistentTail (ECDLP.Canonical.Layout.fieldWidth E) m stored
  have framed := readBorrowedClassical_split_right (Recovery.PublicInput.terminal_disjoint E m)
    (terminal_noBorrowedClassical E m) tail
  have sameFrame := frame_store_eq_of_borrowed_eq E m
    (Recovery.PublicInput.store E m problem.generator.toMathlib problem.target.toMathlib)
    (split (Recovery.PublicInput.terminal_disjoint E m) tail).2
    (eq_of_heq (same.trans
      ((persistentTail_borrowed (ECDLP.Canonical.Layout.fieldWidth E) m stored).trans framed)))
  have joined := join_split_store (Recovery.PublicInput.terminal_disjoint E m) tail
  have baseRead := contextUnion_read_join_right (Recovery.PublicInput.terminal_disjoint E m)
    (split (Recovery.PublicInput.terminal_disjoint E m) tail).1
    (split (Recovery.PublicInput.terminal_disjoint E m) tail).2 (Recovery.PublicInput.baseRef E m)
  have targetRead := contextUnion_read_join_right (Recovery.PublicInput.terminal_disjoint E m)
    (split (Recovery.PublicInput.terminal_disjoint E m) tail).1
    (split (Recovery.PublicInput.terminal_disjoint E m) tail).2 (Recovery.PublicInput.targetRef E m)
  rw [joined] at baseRead targetRead
  constructor
  · rw [← persistentTail_read]
    change tail.read (inputRight (Recovery.PublicInput.terminal_disjoint E m)
      (Recovery.PublicInput.baseRef E m)) = _
    erw [baseRead, ← sameFrame]
    exact Recovery.PublicInput.store_base E m _ _
  · rw [← persistentTail_read]
    change tail.read (inputRight (Recovery.PublicInput.terminal_disjoint E m)
      (Recovery.PublicInput.targetRef E m)) = _
    erw [targetRead, ← sameFrame]
    exact Recovery.PublicInput.store_target E m _ _

/-- Every actual persistent prefix carries the originally supplied public points. -/
lemma persistentProgram_supported_points
    (code : Circuit Model (Recovery.PublicInput.frame E m)
      (persistentCtx (Recovery.PublicInput.context E m) (ECDLP.Canonical.Layout.fieldWidth E) m))
    {Reference : Register} (original : Input (Recovery.PublicInput.frame E m) Reference)
    (record : Store (persistentCtx (Recovery.PublicInput.context E m)
      (ECDLP.Canonical.Layout.fieldWidth E) m) ×
        (Unit × (Store (Recovery.PublicInput.frame E m) × code.Path)))
    (positive :
      0 < ((code.execute environment Reference (enteredState E m problem original)).block
        record).mass) :
    record.1.read (persistentInput (ECDLP.Canonical.Layout.fieldWidth E) m
      (Recovery.PublicInput.contextBaseRef E m)) =
        ECDLP.Canonical.Runtime.Context.pointValue E problem.generator.toMathlib ∧
      record.1.read (persistentInput (ECDLP.Canonical.Layout.fieldWidth E) m
        (Recovery.PublicInput.contextTargetRef E m)) =
        ECDLP.Canonical.Runtime.Context.pointValue E problem.target.toMathlib := by
  have restored := code.borrowedRestored_of_noBorrowedQuantum (environment := environment)
    (show (Recovery.PublicInput.frame E m).borrowedQuantumWires = [] from rfl)
    Reference (enteredState E m problem original)
  obtain ⟨previous, present, same⟩ := code.borrowedRestored_supported_initial
    Reference (enteredState E m problem original) _ restored record positive
  unfold enteredState oracleInput prescribedInput at present
  rw [ExecutionState.executionState_mapClassical_comp,
    ExecutionState.executionState_mapClassical_comp] at present
  obtain ⟨source, equality, _⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff original.state _ previous).mp present
  have prescribed : Recovery.PublicInput.store E m problem.generator.toMathlib
    problem.target.toMathlib =
      previous.1 := congrArg Prod.fst equality
  apply persistent_points_of_borrowed E m problem record.1
  exact (heq_of_eq (congrArg Store.readBorrowedClassical prescribed)).trans
    ((heq_of_eq same).trans (borrowed_transport_heq code record.1.readBorrowedClassical))

/-- The native checker's point interpretations follow internally on every real prefix. -/
lemma persistentProgram_supported_represents
    (code : Circuit Model (Recovery.PublicInput.frame E m)
      (persistentCtx (Recovery.PublicInput.context E m) (ECDLP.Canonical.Layout.fieldWidth E) m))
    {Reference : Register} (original : Input (Recovery.PublicInput.frame E m) Reference)
    (record : Store (persistentCtx (Recovery.PublicInput.context E m)
      (ECDLP.Canonical.Layout.fieldWidth E) m) ×
        (Unit × (Store (Recovery.PublicInput.frame E m) × code.Path)))
    (positive :
      0 < ((code.execute environment Reference (enteredState E m problem original)).block
        record).mass) :
    QuantumAlg.ClassicalRoutines.EllipticCurve.PointRepresents
      (ECDLP.Canonical.Layout.curveSpec E)
      (record.1.read (persistentInput (ECDLP.Canonical.Layout.fieldWidth E) m
        (Recovery.PublicInput.contextBaseRef E m))) problem.generator.toMathlib ∧
      QuantumAlg.ClassicalRoutines.EllipticCurve.PointRepresents
      (ECDLP.Canonical.Layout.curveSpec E)
        (record.1.read (persistentInput (ECDLP.Canonical.Layout.fieldWidth E) m
          (Recovery.PublicInput.contextTargetRef E m))) problem.target.toMathlib := by
  obtain ⟨baseValue, targetValue⟩ :=
    persistentProgram_supported_points E m problem code original record positive
  rw [baseValue, targetValue]
  exact ⟨ECDLP.Measured.publicPoint_represents E problem.generator,
    ECDLP.Measured.publicPoint_represents E problem.target⟩

end

end Support
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
