/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Fiber.Retained
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Instrument.Stored
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Coordinates
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement.Correctness
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Placement.Framing
import all QuantumAlg.Core.Execution.Context.Permutation.State
import all QuantumAlg.Core.Execution.Context.Relabeling.State
import all QuantumAlg.Core.Execution.Context.Union.State

/-!
# Original measured scalar step at every complete Store and old-history fiber

The executed circuit is the native MeasuredPlacement.step, including its real
relabel/frame/permutation embeddings. No replacement point implementation or good-domain
premise occurs. The retained tag below indexes classical history only. Every quantum
exponent and resident quantum frame remains inside the arbitrary joint density matrix.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
namespace Measured

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open ScalarMultiplication.MeasuredPlacement Recovery.Point
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

attribute [local irreducible] Recovery.Point.Instrument.pointKraus
  NumeratorMeasurement.context

/-- Equal input matrices induce equal finite Kraus sums. -/
private lemma krausSum_input_congr {Basis Outcome : Type}
    [Fintype Basis] [Fintype Outcome] (kernel : Outcome → Matrix Basis Basis ℂ)
    {first second : Matrix Basis Basis ℂ} (same : first = second) :
    (∑ outcome, kernel outcome * first * (kernel outcome).conjTranspose) =
      ∑ outcome, kernel outcome * second * (kernel outcome).conjTranspose := by
  exact congrArg (fun matrix =>
    ∑ outcome, kernel outcome * matrix * (kernel outcome).conjTranspose) same

/-- A predicate on existing classical history survives the actual five-stage point body. -/
lemma oldBody_store_history_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (MeasuredPointAddition.context p.size)) (predicate : History → Prop)
    (allowAllocation : Bool := true) :
    (((MeasuredPointAddition.body E Q allowAllocation).execute environment Reference
      state).filterClassical
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ division : Store (MeasuredPointAddition.context p.size),
        Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference division
          stored *
          (state.filterClassical (fun record => predicate record.2.2)).quantumMarginal.matrix *
          (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
            division stored).conjTranspose := by
  have actual := (MeasuredPointAddition.body E Q allowAllocation).execute_mapHistory environment
    Reference state
    (fun history => (history, decide (predicate history)))
  have selected := oldPointBody_store_retained_fiber (environment := environment)
    E Q (Tag := historyPredicateTag)
    (state.mapHistory (fun record =>
      (record.1, (record.2, decide (predicate record.2))))) stored (true : Bool) allowAllocation
  have observed := congrArg (fun result : State (MeasuredPointAddition.context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        ((History × Bool) × (MeasuredPointAddition.body E Q allowAllocation).Path)) =>
    (result.filterClassical (fun record =>
      record.1 = stored ∧ record.2.2.1.2 = true)).quantumMarginal.matrix) actual
  have selectedMatrix := observed.symm.trans selected
  dsimp only [State.mapHistory] at selectedMatrix
  have outputPredicate :
      (fun record : Store (MeasuredPointAddition.context p.size) ×
          (ClassicalOracleModel.empty.HiddenState ×
            (History × (MeasuredPointAddition.body E Q allowAllocation).Path)) =>
        record.1 = stored ∧ decide (predicate record.2.2.1) = true) =
        (fun record => record.1 = stored ∧ predicate record.2.2.1) := by
    funext record
    simp only [decide_eq_true_eq]
  have inputPredicate :
      (fun record : Store (MeasuredPointAddition.context p.size) ×
          (ClassicalOracleModel.empty.HiddenState × History) =>
        decide (predicate record.2.2) = true) =
        (fun record => predicate record.2.2) := by
    funext record
    simp only [decide_eq_true_eq]
  refine Eq.trans ?_ (selectedMatrix.trans ?_)
  · refine (cells_filter_matrix_predicate_congr
      ((MeasuredPointAddition.body E Q allowAllocation).execute environment Reference state)
      outputPredicate.symm
      (secondDecision := fun _ => Classical.propDecidable _)).trans ?_
    exact (cells_map_filter_matrix_decisions
      ((MeasuredPointAddition.body E Q allowAllocation).execute environment Reference state)
      (fun record => (record.1,
        (record.2.1, ((record.2.2.1, decide (predicate record.2.2.1)), record.2.2.2))))
      (fun record => record.1 = stored ∧ record.2.2.1.2 = true)
      (inputDecision := fun _ => Classical.propDecidable _)).symm
  · apply krausSum_input_congr
    exact (cells_map_filter_matrix_decisions state
      (fun record => (record.1, (record.2.1, (record.2.2, decide (predicate record.2.2)))))
      (fun record => record.2.2.2 = true)
      (inputDecision := fun _ => Classical.propDecidable _)).trans
        (cells_filter_matrix_predicate_congr state inputPredicate
          (firstDecision := fun _ => Classical.propDecidable _))

/-- Pull an arbitrary finite-label predicate through the production relabel coordinates. -/
private lemma relabel_filter_matrix {ctx : RuntimeCtx .quantum}
    (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (predicate : Store (ctx.relabel keys physical) × History → Prop) :
    ((ContextRelabeling.state keys physical state).filterClassical
      predicate).quantumMarginal.matrix =
      (state.filterClassical (fun record =>
        predicate (ContextRelabeling.storeEquiv keys physical ctx record.1,
          record.2))).quantumMarginal.matrix.submatrix
            (ContextRelabeling.referenceBasis (source := ctx) keys physical Reference).symm
            (ContextRelabeling.referenceBasis (source := ctx) keys physical Reference).symm := by
  let coordinates := ContextRelabeling.referenceBasis (source := ctx) keys physical Reference
  let labels := ContextRelabeling.recordEquiv (source := ctx) keys physical History
  let mapped : ExecutionState (Store (ctx.relabel keys physical) × History)
      (ctx.register.prod Reference) := state.mapClassical labels
  have stateSame : ContextRelabeling.state keys physical state =
      mapped.reindex coordinates := by
    unfold ContextRelabeling.state
    exact congrArg (fun result : ExecutionState (Store (ctx.relabel keys physical) × History)
        (ctx.register.prod Reference) => result.reindex coordinates)
      (ExecutionState.executionState_mapClassical_congr state rfl)
  refine (congrArg (fun result : State (ctx.relabel keys physical) Reference History =>
    (result.filterClassical predicate).quantumMarginal.matrix) stateSame).trans ?_
  refine (cells_reindex_filter_matrix_decisions
    (C := Store (ctx.relabel keys physical) × History)
    (R := ctx.register.prod Reference)
    (S := (ctx.relabel keys physical).register.prod Reference)
    mapped coordinates predicate
    (inputDecision := fun _ => Classical.propDecidable _)).trans ?_
  apply congrArg (fun matrix : HilbertOperator (ctx.register.prod Reference) =>
    matrix.submatrix coordinates.symm coordinates.symm)
  exact cells_map_filter_matrix_decisions
    (C := Store ctx × History) (D := Store (ctx.relabel keys physical) × History)
    state labels predicate (mapDecision := inferInstance)
    (outputDecision := fun _ => Classical.propDecidable _)

/-- Pull an arbitrary finite-label predicate through the production entry permutation. -/
private lemma permutation_filter_matrix {source target : RuntimeCtx .quantum}
    (same : source.entries.Perm target.entries)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State source Reference History) (predicate : Store target × History → Prop) :
    ((ContextPermutation.state same state).filterClassical predicate).quantumMarginal.matrix =
      (state.filterClassical (fun record =>
        predicate (ContextPermutation.storeEquiv same record.1,
          record.2))).quantumMarginal.matrix.submatrix
            (ContextPermutation.referenceBasis same Reference).symm
            (ContextPermutation.referenceBasis same Reference).symm := by
  let coordinates := ContextPermutation.referenceBasis same Reference
  let labels := ContextPermutation.recordEquiv same History
  let mapped : ExecutionState (Store target × History) (source.register.prod Reference) :=
    state.mapClassical labels
  have stateSame : ContextPermutation.state same state = mapped.reindex coordinates := by
    unfold ContextPermutation.state
    exact congrArg (fun result : ExecutionState (Store target × History)
        (source.register.prod Reference) => result.reindex coordinates)
      (ExecutionState.executionState_mapClassical_congr state rfl)
  refine (congrArg (fun result : State target Reference History =>
    (result.filterClassical predicate).quantumMarginal.matrix) stateSame).trans ?_
  refine (cells_reindex_filter_matrix_decisions
    (C := Store target × History) (R := source.register.prod Reference)
    (S := target.register.prod Reference) mapped coordinates predicate
    (inputDecision := fun _ => Classical.propDecidable _)).trans ?_
  apply congrArg (fun matrix : HilbertOperator (source.register.prod Reference) =>
    matrix.submatrix coordinates.symm coordinates.symm)
  exact cells_map_filter_matrix_decisions
    (C := Store source × History) (D := Store target × History)
    state labels predicate (mapDecision := inferInstance)
    (outputDecision := fun _ => Classical.propDecidable _)

/-- Retain both complete Store components while moving the resident quantum frame to Reference. -/
private lemma splitService_filter_matrix (left right : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint left right)
    {Reference : Register} {Hidden History : Type} [Fintype Hidden] [Fintype History]
    (state : State (left.disjointUnion right separate) Reference (Hidden × History))
    (predicate : Store left × (Hidden × (Store right × History)) → Prop) :
    ((ContextUnion.splitServiceState left right separate state).filterClassical
      predicate).quantumMarginal.matrix =
      (state.filterClassical (fun record =>
        predicate ((ContextUnion.storeEquiv separate record.1).1,
          (record.2.1, ((ContextUnion.storeEquiv separate record.1).2,
            record.2.2))))).quantumMarginal.matrix.submatrix
              (ContextUnion.referenceBasis left right separate Reference).symm
              (ContextUnion.referenceBasis left right separate Reference).symm := by
  let coordinates := ContextUnion.referenceBasis left right separate Reference
  let split : State left (right.register.prod Reference) (Store right × (Hidden × History)) :=
    ContextUnion.splitState left right separate state
  let arrange : Store left × (Store right × (Hidden × History)) →
      Store left × (Hidden × (Store right × History)) :=
    fun record => (record.1, ContextUnion.serviceHistory right Hidden History record.2)
  let selected : Store left × (Store right × (Hidden × History)) → Prop :=
    fun record => predicate (arrange record)
  have arrangeSame : ContextUnion.splitServiceState left right separate state =
      split.mapClassical arrange := by
    dsimp only [ContextUnion.splitServiceState, State.mapHistory, split]
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  refine (congrArg (fun result : State left (right.register.prod Reference)
      (Hidden × (Store right × History)) =>
    (result.filterClassical predicate).quantumMarginal.matrix) arrangeSame).trans ?_
  refine (cells_map_filter_matrix_decisions
    (C := Store left × (Store right × (Hidden × History)))
    (D := Store left × (Hidden × (Store right × History)))
    split arrange predicate (mapDecision := inferInstance)
    (inputDecision := fun _ => Classical.propDecidable _)).trans ?_
  let labels := ContextUnion.recordEquiv left right separate (Hidden × History)
  let mapped : ExecutionState (Store left × (Store right × (Hidden × History)))
      ((left.disjointUnion right separate).register.prod Reference) :=
    state.mapClassical labels
  have splitSame : split = mapped.reindex coordinates := by
    dsimp only [split, ContextUnion.splitState]
    exact congrArg (fun result : ExecutionState
        (Store left × (Store right × (Hidden × History)))
        ((left.disjointUnion right separate).register.prod Reference) =>
      result.reindex coordinates)
      (ExecutionState.executionState_mapClassical_congr state rfl)
  refine (congrArg (fun result : State left (right.register.prod Reference)
      (Store right × (Hidden × History)) =>
    (@ExecutionState.filterClassical _ _ _ result selected
      (fun _ => Classical.propDecidable _)).quantumMarginal.matrix) splitSame).trans ?_
  refine (cells_reindex_filter_matrix_decisions
    (C := Store left × (Store right × (Hidden × History)))
    (R := (left.disjointUnion right separate).register.prod Reference)
    (S := left.register.prod (right.register.prod Reference))
    mapped coordinates selected
    (outputDecision := fun _ => Classical.propDecidable _)
    (inputDecision := fun _ => Classical.propDecidable _)).trans ?_
  apply congrArg (fun matrix : HilbertOperator
      ((left.disjointUnion right separate).register.prod Reference) =>
    matrix.submatrix coordinates.symm coordinates.symm)
  exact cells_map_filter_matrix_decisions
    (C := Store (left.disjointUnion right separate) × (Hidden × History))
    (D := Store left × (Store right × (Hidden × History)))
    state labels selected (mapDecision := inferInstance)
    (outputDecision := fun _ => Classical.propDecidable _)

private lemma splitService_store_history_matrix (left right : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint left right)
    {Reference : Register} {Hidden History : Type} [Fintype Hidden] [Fintype History]
    (state : State (left.disjointUnion right separate) Reference (Hidden × History))
    (stored : Store (left.disjointUnion right separate)) (predicate : History → Prop) :
    ((ContextUnion.splitServiceState left right separate state).filterClassical
      (fun record => record.1 = (ContextUnion.storeEquiv separate stored).1 ∧
        record.2.2.1 = (ContextUnion.storeEquiv separate stored).2 ∧
          predicate record.2.2.2)).quantumMarginal.matrix =
      (state.filterClassical (fun record =>
        record.1 = stored ∧ predicate record.2.2)).quantumMarginal.matrix.submatrix
          (ContextUnion.referenceBasis left right separate Reference).symm
          (ContextUnion.referenceBasis left right separate Reference).symm := by
  let selected : Store left × (Hidden × (Store right × History)) → Prop :=
    fun record => record.1 = (ContextUnion.storeEquiv separate stored).1 ∧
      record.2.2.1 = (ContextUnion.storeEquiv separate stored).2 ∧ predicate record.2.2.2
  refine (cells_filter_matrix_predicate_congr
    (ContextUnion.splitServiceState left right separate state)
    (rfl : selected = selected)
    (secondDecision := fun _ => Classical.propDecidable _)).trans ?_
  refine (splitService_filter_matrix left right separate state selected).trans ?_
  have same (original : Store (left.disjointUnion right separate)) :
      (ContextUnion.storeEquiv separate original).1 =
          (ContextUnion.storeEquiv separate stored).1 ∧
        (ContextUnion.storeEquiv separate original).2 =
          (ContextUnion.storeEquiv separate stored).2 ↔ original = stored := by
    constructor
    · intro equal
      exact (ContextUnion.storeEquiv separate).injective (Prod.ext equal.1 equal.2)
    · intro equal
      subst original
      exact ⟨rfl, rfl⟩
  apply congrArg (fun matrix : HilbertOperator
      ((left.disjointUnion right separate).register.prod Reference) =>
    matrix.submatrix (ContextUnion.referenceBasis left right separate Reference).symm
      (ContextUnion.referenceBasis left right separate Reference).symm)
  apply cells_filter_matrix_predicate_congr state
    (firstDecision := fun _ => Classical.propDecidable _)
  funext record
  apply propext
  dsimp only [selected]
  simp only [← and_assoc, same]

private lemma submatrix_roundtrip {A B : Type} (coordinates : A ≃ B)
    (matrix : Matrix A A ℂ) :
    (matrix.submatrix coordinates.symm coordinates.symm).submatrix
      coordinates coordinates = matrix := by
  ext row column
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]

/-- Reindex a finite Kraus sum before specializing to the physical execution context. -/
private lemma reindexKrausSum {Source Target Outcome : Type}
    [Fintype Source] [Fintype Target] [Fintype Outcome]
    (basis : Target ≃ Source) (kernel : Outcome → Matrix Source Source ℂ)
    (density : Matrix Source Source ℂ) :
    (∑ outcome, kernel outcome * density * (kernel outcome).conjTranspose).submatrix basis basis =
      ∑ outcome, (kernel outcome).submatrix basis basis * density.submatrix basis basis *
        ((kernel outcome).submatrix basis basis).conjTranspose := by
  have product (operator : Matrix Source Source ℂ) :
      (operator * density * operator.conjTranspose).submatrix basis basis =
        operator.submatrix basis basis * density.submatrix basis basis *
          (operator.submatrix basis basis).conjTranspose := by
    calc
      _ = (operator * density).submatrix basis basis *
          operator.conjTranspose.submatrix basis basis :=
        (Matrix.submatrix_mul_equiv (operator * density) operator.conjTranspose
          basis basis basis).symm
      _ = _ :=
        congrArg₂ (fun first second : Matrix Target Target ℂ => first * second)
          (Matrix.submatrix_mul_equiv operator density basis basis basis).symm
          (Matrix.conjTranspose_submatrix operator basis basis).symm
  ext row column
  rw [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro outcome _
  exact congrArg (fun matrix : Matrix Target Target ℂ => matrix row column)
    (product (kernel outcome))

/-- Transport a proved Kraus sum together with its selected input matrix. -/
private lemma transportKrausSum {Source Target Outcome : Type}
    [Fintype Source] [Fintype Target] [Fintype Outcome]
    (basis : Target ≃ Source) (kernel : Outcome → Matrix Source Source ℂ)
    {sourceInput sourceOutput : Matrix Source Source ℂ}
    {targetInput : Matrix Target Target ℂ}
    (sourceLaw : sourceOutput =
      ∑ outcome, kernel outcome * sourceInput * (kernel outcome).conjTranspose)
    (inputFiber : targetInput = sourceInput.submatrix basis basis) :
    sourceOutput.submatrix basis basis =
      ∑ outcome, (kernel outcome).submatrix basis basis * targetInput *
        ((kernel outcome).submatrix basis basis).conjTranspose := by
  rw [sourceLaw, inputFiber]
  exact reindexKrausSum basis kernel sourceInput

/-- The original five-factor kernel in its actual injectively relabelled context. -/
def placedKraus {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (Reference : Register) (division : Store (MeasuredPointAddition.context p.size))
    (stored : Store (MeasuredPointAddition.Placement.context p.size keys physical)) :
    Matrix ((MeasuredPointAddition.Placement.context p.size keys physical).register.prod
      Reference).Index
      ((MeasuredPointAddition.Placement.context p.size keys physical).register.prod
        Reference).Index ℂ :=
  (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference division
    ((ContextRelabeling.storeEquiv keys physical
      (MeasuredPointAddition.context p.size)).symm stored)).submatrix
        (ContextRelabeling.referenceBasis keys physical Reference).symm
        (ContextRelabeling.referenceBasis keys physical Reference).symm

/-- Actual relabelled execution retains each final Store and original history predicate. -/
lemma placedBody_store_history_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.Placement.context p.size keys physical) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (MeasuredPointAddition.Placement.context p.size keys physical))
    (predicate : History → Prop) (allowAllocation : Bool := true) :
    (((MeasuredPointAddition.Placement.body E Q keys physical allowAllocation).execute environment
      Reference
      state).filterClassical (fun record =>
        record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ division : Store (MeasuredPointAddition.context p.size),
        placedKraus (environment := environment) E Q keys physical Reference division stored *
          (state.filterClassical (fun record => predicate record.2.2)).quantumMarginal.matrix *
          (placedKraus (environment := environment) E Q keys physical Reference division
            stored).conjTranspose := by
  obtain ⟨original, rfl⟩ := ContextRelabeling.state_surjective keys physical state
  let placed := MeasuredPointAddition.Placement.context p.size keys physical
  let code : Circuit (.quantum AlgorithmGate.model .empty) placed placed allowAllocation :=
    MeasuredPointAddition.Placement.body E Q keys physical allowAllocation
  let coordinates := ContextRelabeling.referenceBasis
    (source := MeasuredPointAddition.context p.size) keys physical Reference
  let sourceOutput := (MeasuredPointAddition.body E Q false).execute environment Reference original
  let transported := ContextRelabeling.state keys physical sourceOutput
  have actual : code.execute environment Reference (ContextRelabeling.state keys physical
    original) =
      transported :=
    MeasuredPointAddition.Placement.body_execute E Q keys physical original allowAllocation
  have observed := congrArg (fun result : State placed Reference
      (ClassicalOracleModel.empty.HiddenState × (History × code.Path)) =>
    (result.filterClassical (fun record =>
      record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix) actual
  have same (originalStore : Store (MeasuredPointAddition.context p.size)) :
      ContextRelabeling.storeEquiv keys physical _ originalStore = stored ↔
        originalStore = (ContextRelabeling.storeEquiv keys physical _).symm stored := by
    constructor
    · intro equal
      exact (ContextRelabeling.storeEquiv keys physical _).injective
        (equal.trans ((ContextRelabeling.storeEquiv keys physical _).apply_symm_apply stored).symm)
    · intro equal
      rw [equal, Equiv.apply_symm_apply]
  have outputFiber :
      ((code.execute environment Reference (ContextRelabeling.state keys physical
        original)).filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      (sourceOutput.filterClassical (fun record =>
        record.1 = (ContextRelabeling.storeEquiv keys physical _).symm stored ∧
          predicate record.2.2.1)).quantumMarginal.matrix.submatrix
            coordinates.symm coordinates.symm := by
    refine observed.trans ?_
    refine (cells_filter_matrix_predicate_congr transported rfl
      (secondDecision := fun _ => Classical.propDecidable _)).trans ?_
    refine (relabel_filter_matrix keys physical sourceOutput
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).trans ?_
    apply congrArg (fun matrix : HilbertOperator
        ((MeasuredPointAddition.context p.size).register.prod Reference) =>
      matrix.submatrix coordinates.symm coordinates.symm)
    apply cells_filter_matrix_predicate_congr sourceOutput
      (firstDecision := fun _ => Classical.propDecidable _)
    funext record
    exact congrArg (fun selected => selected ∧ predicate record.2.2.1)
      (propext (same record.1))
  have inputFiber :
      ((ContextRelabeling.state keys physical original).filterClassical
        (fun record => predicate record.2.2)).quantumMarginal.matrix =
      (original.filterClassical (fun record =>
        predicate record.2.2)).quantumMarginal.matrix.submatrix
          coordinates.symm coordinates.symm :=
    relabel_filter_matrix keys physical original (fun record => predicate record.2.2)
  have sourceLaw := oldBody_store_history_matrix (environment := environment) E Q original
    ((ContextRelabeling.storeEquiv keys physical
      (MeasuredPointAddition.context p.size)).symm stored) predicate false
  exact outputFiber.trans
    (transportKrausSum coordinates.symm
      (fun division => Recovery.Point.Instrument.pointKraus (environment := environment) E Q
        Reference division
        ((ContextRelabeling.storeEquiv keys physical
          (MeasuredPointAddition.context p.size)).symm stored))
      sourceLaw inputFiber)

/-- The same placed point kernel, now pulled back across the physically resident union. -/
def framedKraus {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey) (physical : Nat ↪ Nat)
    (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint
      (MeasuredPointAddition.Placement.context p.size keys physical) frame)
    (Reference : Register) (division : Store (MeasuredPointAddition.context p.size))
    (stored : Store (MeasuredPointAddition.Placement.Framing.context p.size keys physical
      frame separate)) :
    Matrix ((MeasuredPointAddition.Placement.Framing.context p.size keys physical frame
      separate).register.prod Reference).Index
      ((MeasuredPointAddition.Placement.Framing.context p.size keys physical frame
        separate).register.prod Reference).Index ℂ :=
  (placedKraus (environment := environment) E Q keys physical (frame.register.prod Reference)
    division
    (ContextUnion.storeEquiv separate stored).1).submatrix
      (ContextUnion.referenceBasis _ frame separate Reference)
      (ContextUnion.referenceBasis _ frame separate Reference)

attribute [local irreducible] MeasuredPointAddition.Placement.body

/-- Restoring the frame-history order preserves the selected complete Store and old history. -/
private lemma restore_history_store_filter_matrix {ctx : RuntimeCtx .quantum}
    {Reference : Register} {FrameStore History Path : Type}
    [Fintype FrameStore] [Fintype History] [Fintype Path]
    (state : State ctx Reference
      (ClassicalOracleModel.empty.HiddenState × ((FrameStore × History) × Path)))
    (stored : Store ctx) (frameStore : FrameStore) (predicate : History → Prop) :
    ((state.mapHistory (fun record =>
      (record.1, (record.2.1.1, (record.2.1.2, record.2.2))))).filterClassical (fun record =>
        record.1 = stored ∧ record.2.2.1 = frameStore ∧
          predicate record.2.2.2.1)).quantumMarginal.matrix =
      (state.filterClassical (fun record =>
        record.1 = stored ∧ record.2.2.1.1 = frameStore ∧
          predicate record.2.2.1.2)).quantumMarginal.matrix := by
  dsimp only [State.mapHistory]
  exact cells_map_filter_matrix_decisions state
    (fun record => (record.1, (record.2.1,
      (record.2.2.1.1, (record.2.2.1.2, record.2.2.2)))))
    (fun record => record.1 = stored ∧ record.2.2.1 = frameStore ∧
      predicate record.2.2.2.1)

/-- Splitting a native union selects the same complete output Store and original history. -/
private lemma union_output_store_history_matrix (placed frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint placed frame)
    (child : Circuit (.quantum AlgorithmGate.model .empty) placed placed false)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (placed.disjointUnion frame separate) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (placed.disjointUnion frame separate)) (predicate : History → Prop)
    (allowAllocation : Bool) :
    let coordinates := ContextUnion.referenceBasis placed frame separate Reference
    let code : Circuit (.quantum AlgorithmGate.model .empty)
      (placed.disjointUnion frame separate) (placed.disjointUnion frame separate)
      allowAllocation := .embed (ContextEmbedding.alongUnion placed frame separate) child
    let localInput := ContextUnion.splitServiceState placed frame separate state
    let localOutput := child.execute environment (frame.register.prod Reference) localInput
    ((code.execute environment Reference state).filterClassical (fun record =>
      record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix.submatrix
        coordinates.symm coordinates.symm =
      (localOutput.filterClassical (fun record =>
        record.1 = (ContextUnion.storeEquiv separate stored).1 ∧
          record.2.2.1.1 = (ContextUnion.storeEquiv separate stored).2 ∧
            predicate record.2.2.1.2)).quantumMarginal.matrix := by
  let childStore := (ContextUnion.storeEquiv separate stored).1
  let frameStore := (ContextUnion.storeEquiv separate stored).2
  let localInput := ContextUnion.splitServiceState placed frame separate state
  let localOutput := child.execute environment (frame.register.prod Reference) localInput
  let code : Circuit (.quantum AlgorithmGate.model .empty)
      (placed.disjointUnion frame separate) (placed.disjointUnion frame separate)
      allowAllocation := .embed (ContextEmbedding.alongUnion placed frame separate) child
  let actualOutput := code.execute environment Reference state
  have actual := Circuit.union_embed_execute (environment := environment) (allowAllocation :=
    allowAllocation)
    child frame separate Reference state
  have observed := congrArg (fun result : State placed (frame.register.prod Reference)
      (ClassicalOracleModel.empty.HiddenState × (Store frame × (History × code.Path))) =>
    (result.filterClassical (fun record => record.1 = childStore ∧
      record.2.2.1 = frameStore ∧ predicate record.2.2.2.1)).quantumMarginal.matrix) actual
  have splitFiber := splitService_store_history_matrix placed frame separate
    (Hidden := ClassicalOracleModel.empty.HiddenState) (History := History × code.Path)
    actualOutput stored (fun history => predicate history.1)
  have restored := restore_history_store_filter_matrix localOutput childStore frameStore predicate
  exact splitFiber.symm.trans (observed.trans restored)

/-- Splitting the input retains the resident frame Store and the selected original history. -/
private lemma union_input_store_history_matrix (placed frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint placed frame)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (placed.disjointUnion frame separate) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (frameStore : Store frame) (predicate : History → Prop) :
    ((ContextUnion.splitServiceState placed frame separate state).filterClassical
      (fun record => record.2.2.1 = frameStore ∧ predicate record.2.2.2)).quantumMarginal.matrix =
      (state.filterClassical (fun record =>
        (ContextUnion.storeEquiv separate record.1).2 = frameStore ∧
          predicate record.2.2)).quantumMarginal.matrix.submatrix
            (ContextUnion.referenceBasis placed frame separate Reference).symm
            (ContextUnion.referenceBasis placed frame separate Reference).symm := by
  let localInput := ContextUnion.splitServiceState placed frame separate state
  let coordinates := ContextUnion.referenceBasis placed frame separate Reference
  refine (cells_filter_matrix_predicate_congr localInput rfl
    (secondDecision := fun _ => Classical.propDecidable _)).trans ?_
  refine (splitService_filter_matrix placed frame separate state
    (fun record => record.2.2.1 = frameStore ∧ predicate record.2.2.2)).trans ?_
  apply congrArg (fun matrix : HilbertOperator
      ((placed.disjointUnion frame separate).register.prod Reference) =>
    matrix.submatrix coordinates.symm coordinates.symm)
  exact cells_filter_matrix_predicate_congr state rfl
    (firstDecision := fun _ => Classical.propDecidable _)

/-- Pull a selected local Kraus law back using independently established input and output fibers. -/
private lemma pullbackKrausSum_of_fibers {Caller Child Outcome : Type}
    [Fintype Caller] [Fintype Child] [Fintype Outcome]
    (coordinates : Caller ≃ Child) (kernel : Outcome → Matrix Child Child ℂ)
    (density output : Matrix Caller Caller ℂ)
    (inputMatrix splitInput outputMatrix splitOutput : Matrix Child Child ℂ)
    (outputFiber : output.submatrix coordinates.symm coordinates.symm = splitOutput)
    (inputFiber : splitInput = density.submatrix coordinates.symm coordinates.symm)
    (inputSame : inputMatrix = splitInput) (outputSame : splitOutput = outputMatrix)
    (localLaw : outputMatrix =
      ∑ outcome, kernel outcome * inputMatrix * (kernel outcome).conjTranspose) :
    output = ∑ outcome, (kernel outcome).submatrix coordinates coordinates * density *
      ((kernel outcome).submatrix coordinates coordinates).conjTranspose := by
  exact (submatrix_roundtrip coordinates output).symm.trans
    (cells_pullback_sum_sandwich coordinates kernel density inputMatrix
      (output.submatrix coordinates.symm coordinates.symm)
      (inputSame.trans inputFiber) (outputFiber.trans (outputSame.trans localLaw)))

/-- A finite child instrument retains every complete Store and history fiber under a union. -/
private lemma union_store_history_matrix (placed frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint placed frame)
    (child : Circuit (.quantum AlgorithmGate.model .empty) placed placed false)
    {Outcome : Type} [Fintype Outcome]
    (kernel : (reference : Register) → Outcome → Store placed →
      HilbertOperator (placed.register.prod reference))
    (localLaw : ∀ (reference : Register) {History : Type} [Fintype History]
      (state : State placed reference (ClassicalOracleModel.empty.HiddenState × History))
      (stored : Store placed) (predicate : History → Prop),
      ((child.execute environment reference state).filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
        ∑ outcome : Outcome, kernel reference outcome stored *
          (state.filterClassical (fun record => predicate record.2.2)).quantumMarginal.matrix *
          (kernel reference outcome stored).conjTranspose)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (placed.disjointUnion frame separate) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (placed.disjointUnion frame separate)) (predicate : History → Prop)
    (allowAllocation : Bool) :
    let coordinates := ContextUnion.referenceBasis placed frame separate Reference
    let childStore := (ContextUnion.storeEquiv separate stored).1
    let frameStore := (ContextUnion.storeEquiv separate stored).2
    let lifted := fun outcome : Outcome =>
      (kernel (frame.register.prod Reference) outcome childStore).submatrix
        coordinates coordinates
    (((Circuit.embed (allowAllocation := allowAllocation)
      (ContextEmbedding.alongUnion placed frame separate) child).execute environment Reference
        state).filterClassical (fun record =>
          record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ outcome : Outcome, lifted outcome *
        (state.filterClassical (fun record =>
          (ContextUnion.storeEquiv separate record.1).2 = frameStore ∧
            predicate record.2.2)).quantumMarginal.matrix *
          (lifted outcome).conjTranspose := by
  let coordinates := ContextUnion.referenceBasis placed frame separate Reference
  let childStore := (ContextUnion.storeEquiv separate stored).1
  let frameStore := (ContextUnion.storeEquiv separate stored).2
  let localInput := ContextUnion.splitServiceState placed frame separate state
  have outputFiber := union_output_store_history_matrix (environment := environment)
    placed frame separate child
    state stored predicate allowAllocation
  have inputFiber := union_input_store_history_matrix placed frame separate state frameStore
    predicate
  have selectedLaw := localLaw (frame.register.prod Reference) localInput childStore
    (fun history => history.1 = frameStore ∧ predicate history.2)
  refine pullbackKrausSum_of_fibers coordinates
    (fun outcome : Outcome => kernel (frame.register.prod Reference) outcome childStore)
    _ _ _ _ _ _ outputFiber inputFiber ?_ ?_ selectedLaw
  · exact cells_filter_matrix_predicate_congr localInput rfl
  · exact cells_filter_matrix_predicate_congr
      (child.execute environment (frame.register.prod Reference) localInput) rfl

/-- The actual native framing retains exactly the original complete frame Store. -/
lemma framedBody_store_history_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (keys : StorageKey ↪ StorageKey)
    (physical : Nat ↪ Nat) (frame : RuntimeCtx .quantum)
    (separate : RuntimeCtx.StorageDisjoint
      (MeasuredPointAddition.Placement.context p.size keys physical) frame)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.Placement.Framing.context p.size keys physical
      frame separate) Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (MeasuredPointAddition.Placement.Framing.context p.size keys physical
      frame separate)) (predicate : History → Prop) (allowAllocation : Bool := true) :
    (((MeasuredPointAddition.Placement.Framing.body E Q keys physical frame separate
      allowAllocation).execute environment Reference state).filterClassical (fun record =>
        record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ division : Store (MeasuredPointAddition.context p.size),
        framedKraus (environment := environment) E Q keys physical frame separate Reference
          division stored *
          (state.filterClassical (fun record =>
            (ContextUnion.storeEquiv separate record.1).2 =
              (ContextUnion.storeEquiv separate stored).2 ∧
                predicate record.2.2)).quantumMarginal.matrix *
          (framedKraus (environment := environment) E Q keys physical frame separate Reference
            division stored).conjTranspose := by
  exact union_store_history_matrix
    (MeasuredPointAddition.Placement.context p.size keys physical) frame separate
    (MeasuredPointAddition.Placement.body E Q keys physical false)
    (fun reference division finalStore =>
      placedKraus (environment := environment) E Q keys physical reference division finalStore)
    (fun reference {history} _ input finalStore selected =>
      placedBody_store_history_matrix E Q keys physical
        (Reference := reference) (History := history) input finalStore selected false)
    state stored predicate allowAllocation

/-- The old step's complete final Store in its actual point/ambient decomposition. -/
def pointStore (width : Nat) {count : Nat} (active : Fin count) :
    Store (readyContext width count) ≃
      Store (MeasuredPointAddition.context width) × Store (ambientContext width active) :=
  (ContextPermutation.storeEquiv (framed_entries width active)).symm.trans
    ((ContextUnion.storeEquiv (ambient_disjoint width active)).trans
      ((ContextRelabeling.storeEquiv (storageMap width active) (physicalMap width active)
        (MeasuredPointAddition.context width)).symm.prodCongr (Equiv.refl _)))

/-- Exact old indexed-step kernel; all five point factors remain in their original order. -/
def stepKraus {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (Reference : Register)
    (division : Store (MeasuredPointAddition.context p.size))
    (stored : Store (readyContext p.size count)) :
    Matrix ((readyContext p.size count).register.prod Reference).Index
      ((readyContext p.size count).register.prod Reference).Index ℂ :=
  (framedKraus (environment := environment) E Q (storageMap p.size active) (physicalMap p.size
    active)
    (ambientContext p.size active) (ambient_disjoint p.size active) Reference division
    ((ContextPermutation.storeEquiv (framed_entries p.size active)).symm stored)).submatrix
      (ContextPermutation.referenceBasis (framed_entries p.size active) Reference).symm
      (ContextPermutation.referenceBasis (framed_entries p.size active) Reference).symm

/-- Original point/ambient/reference basis read directly from the production step coordinates. -/
def stepCoordinates (width : Nat) {count : Nat} (active : Fin count) (Reference : Register) :
    ((readyContext width count).register.prod Reference).Index ≃
      ((MeasuredPointAddition.context width).register.prod
        ((ambientContext width active).register.prod Reference)).Index :=
  ((pointBasis width active).prodCongr (Equiv.refl Reference.Index)).trans
    (Equiv.prodAssoc _ _ _)

lemma stepKraus_original_point {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (Reference : Register)
    (division : Store (MeasuredPointAddition.context p.size))
    (stored : Store (readyContext p.size count)) :
    stepKraus (environment := environment) E Q active Reference division stored =
      (Recovery.Point.Instrument.pointKraus (environment := environment) E Q
        ((ambientContext p.size active).register.prod Reference) division
        (pointStore p.size active stored).1).submatrix
          (stepCoordinates p.size active Reference) (stepCoordinates p.size active Reference) := by
  ext row column
  rfl

/-- Transport the input fiber and its CP sum before observing the indexed output history. -/
private lemma step_input_transport_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {count : Nat} (active : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (original : State (MeasuredPointAddition.Placement.Framing.context p.size
      (storageMap p.size active) (physicalMap p.size active)
      (ambientContext p.size active) (ambient_disjoint p.size active)) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (readyContext p.size count)) (predicate : History → Prop) :
    let same := framed_entries p.size active
    let coordinates := ContextPermutation.referenceBasis same Reference
    let originalStore := (ContextPermutation.storeEquiv same).symm stored
    let sourceOutput := (residentBody E Q active).execute environment Reference original
    (sourceOutput.filterClassical (fun record =>
      record.1 = originalStore ∧ predicate record.2.2.1)).quantumMarginal.matrix.submatrix
        coordinates.symm coordinates.symm =
      ∑ division : Store (MeasuredPointAddition.context p.size),
        stepKraus (environment := environment) E Q active Reference division stored *
          ((ContextPermutation.state same original).filterClassical (fun record =>
            (pointStore p.size active record.1).2 = (pointStore p.size active stored).2 ∧
              predicate record.2.2)).quantumMarginal.matrix *
          (stepKraus (environment := environment) E Q active Reference division
            stored).conjTranspose := by
  dsimp only
  let same := framed_entries p.size active
  let caller := MeasuredPointAddition.Placement.Framing.context p.size
    (storageMap p.size active) (physicalMap p.size active)
    (ambientContext p.size active) (ambient_disjoint p.size active)
  let child : Circuit (.quantum AlgorithmGate.model .empty) caller caller false :=
    residentBody E Q active
  let coordinates := ContextPermutation.referenceBasis same Reference
  let originalStore := (ContextPermutation.storeEquiv same).symm stored
  let sourceOutput := child.execute environment Reference original
  have retained (before : Store caller) :
      (pointStore p.size active (ContextPermutation.storeEquiv same before)).2 =
        (ContextUnion.storeEquiv (ambient_disjoint p.size active) before).2 := by
    change (ContextUnion.storeEquiv (ambient_disjoint p.size active)
      ((ContextPermutation.storeEquiv same).symm
        (ContextPermutation.storeEquiv same before))).2 = _
    rw [Equiv.symm_apply_apply]
  have inputFiber :
      ((ContextPermutation.state same original).filterClassical (fun record =>
        (pointStore p.size active record.1).2 = (pointStore p.size active stored).2 ∧
          predicate record.2.2)).quantumMarginal.matrix =
      (original.filterClassical (fun record =>
        (ContextUnion.storeEquiv (ambient_disjoint p.size active) record.1).2 =
          (ContextUnion.storeEquiv (ambient_disjoint p.size active) originalStore).2 ∧
            predicate record.2.2)).quantumMarginal.matrix.submatrix
              coordinates.symm coordinates.symm := by
    refine (cells_filter_matrix_predicate_congr
      (ContextPermutation.state same original) rfl
      (secondDecision := fun _ => Classical.propDecidable _)).trans ?_
    refine (permutation_filter_matrix same original (fun record =>
      (pointStore p.size active record.1).2 = (pointStore p.size active stored).2 ∧
        predicate record.2.2)).trans ?_
    apply congrArg (fun matrix : HilbertOperator (caller.register.prod Reference) =>
      matrix.submatrix coordinates.symm coordinates.symm)
    apply cells_filter_matrix_predicate_congr original
      (firstDecision := fun _ => Classical.propDecidable _)
    funext record
    rw [retained]
    rfl
  have sourceLaw := framedBody_store_history_matrix (environment := environment) E Q
    (storageMap p.size active) (physicalMap p.size active)
    (ambientContext p.size active) (ambient_disjoint p.size active)
    original originalStore predicate false
  exact transportKrausSum coordinates.symm
    (fun division : Store (MeasuredPointAddition.context p.size) =>
      framedKraus (environment := environment) E Q (storageMap p.size active) (physicalMap p.size
        active)
        (ambientContext p.size active) (ambient_disjoint p.size active)
        Reference division originalStore)
    sourceLaw inputFiber

/-- The production indexed step, with complete Store, arbitrary dirty quantum input and history. -/
lemma step_store_history_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {count : Nat} (active : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (readyContext p.size count)) (predicate : History → Prop)
    (allowAllocation : Bool := true) :
    (((step E Q active allowAllocation).execute environment Reference state).filterClassical (fun
      record =>
      record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ division : Store (MeasuredPointAddition.context p.size),
        stepKraus (environment := environment) E Q active Reference division stored *
          (state.filterClassical (fun record =>
            (pointStore p.size active record.1).2 = (pointStore p.size active stored).2 ∧
              predicate record.2.2)).quantumMarginal.matrix *
          (stepKraus (environment := environment) E Q active Reference division
            stored).conjTranspose := by
  let same := framed_entries p.size active
  let caller := MeasuredPointAddition.Placement.Framing.context p.size
    (storageMap p.size active) (physicalMap p.size active)
    (ambientContext p.size active) (ambient_disjoint p.size active)
  let child : Circuit (.quantum AlgorithmGate.model .empty) caller caller false :=
    residentBody E Q active
  let code : Circuit (.quantum AlgorithmGate.model .empty)
      (readyContext p.size count) (readyContext p.size count) allowAllocation :=
    step E Q active allowAllocation
  let coordinates := ContextPermutation.referenceBasis same Reference
  let originalStore := (ContextPermutation.storeEquiv same).symm stored
  obtain ⟨original, rfl⟩ := ContextPermutation.state_surjective same state
  let sourceOutput := child.execute environment Reference original
  let transported := ContextPermutation.state same sourceOutput
  have actual : code.execute environment Reference (ContextPermutation.state same original) =
      transported := step_execute E Q active original allowAllocation
  have observed := congrArg (fun result : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × (History × code.Path)) =>
    (result.filterClassical (fun record =>
      record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix) actual
  have sameStore (before : Store caller) :
      ContextPermutation.storeEquiv same before = stored ↔ before = originalStore := by
    constructor
    · intro equal
      exact (ContextPermutation.storeEquiv same).injective
        (equal.trans ((ContextPermutation.storeEquiv same).apply_symm_apply stored).symm)
    · intro equal
      rw [equal]
      exact (ContextPermutation.storeEquiv same).apply_symm_apply stored
  have outputFiber :
      ((code.execute environment Reference (ContextPermutation.state same original)).filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      (sourceOutput.filterClassical (fun record =>
        record.1 = originalStore ∧ predicate record.2.2.1)).quantumMarginal.matrix.submatrix
          coordinates.symm coordinates.symm := by
    refine observed.trans ?_
    refine (cells_filter_matrix_predicate_congr transported rfl
      (secondDecision := fun _ => Classical.propDecidable _)).trans ?_
    refine (permutation_filter_matrix same sourceOutput
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).trans ?_
    apply congrArg (fun matrix : HilbertOperator (caller.register.prod Reference) =>
      matrix.submatrix coordinates.symm coordinates.symm)
    apply cells_filter_matrix_predicate_congr sourceOutput
      (firstDecision := fun _ => Classical.propDecidable _)
    funext record
    exact congrArg (fun selected => selected ∧ predicate record.2.2.1)
      (propext (sameStore record.1))
  exact outputFiber.trans
    (step_input_transport_matrix E Q active original stored predicate)

end

end Measured
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
