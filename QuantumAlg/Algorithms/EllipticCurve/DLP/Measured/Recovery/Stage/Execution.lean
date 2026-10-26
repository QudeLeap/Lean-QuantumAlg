/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Store.Join
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Layout.Union.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Program
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Instrument.Stored
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Fiber.Retained
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Correctness
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Stored.Fibers
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Observation
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Values
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Workspace.Placement
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Stage.Blocks
import all QuantumAlg.Components.QuditShift.Qubit
import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.Circuit.ClassicalTag.Encoding
import all QuantumAlg.Core.Execution.Circuit.History
import all QuantumAlg.Core.Execution.State.History
import all QuantumAlg.Core.Execution.Store.History
import all QuantumAlg.Core.Execution.Store.MarginalSum
import all QuantumAlg.Core.Execution.Unitary.StoreFilter
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Core.Execution.Measured.Stage
import all QuantumAlg.Core.Execution.Measured.FeedForward
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Algorithm.ExecutionState.Map
import all Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Stored-density instrument for a measured ECC streaming stage

The literal fixed-context point body, point Kraus operator, native preparation word,
complete Store descriptors and Reference coordinates remain in their mathematical owners
and are composed here.

The complete original stage statement keeps arbitrary input Store/history,
dirty bank and external Reference. Its point, feedback, preparation, actual
measurement write and same-cell reset stay in their original temporal order.
-/

open QuantumAlg.EllipticCurve

attribute [local irreducible] QuantumAlg.ContextEmbedding.basis QuantumAlg.ContextEmbedding.store

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

def preparationWires (width m : Nat) : Fin 2 ↪ Fin (terminal width m).systemCount where
  toFun index := position width m index.castSucc
  inj' := by
    intro left right same
    have physical := congrArg
      (fun wire => ((terminal width m).quantumLayout.wire wire).identity) same
    rw [position_wire, position_wire] at physical
    apply Fin.ext
    exact Nat.add_left_cancel physical

lemma preparation_dimensions (width m : Nat) (index : Fin 2) :
    (Recovery.Point.Program.layout.wire index).dimension =
      ((terminal width m).quantumLayout.wire (preparationWires width m index)).dimension := by
  exact (position_qubit width m index.castSucc).symm

def preparation (width m r remaining : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty (terminal width m).quantumLayout :=
  UnitaryCircuit.placeAt _ _ (preparationWires width m)
    (preparation_dimensions width m) (Recovery.Point.Program.step r remaining)

def order (m : Nat) : List (Fin (2 * m)) := List.finRange (2 * m)

def remaining (m : Nat) (index : Fin (2 * m)) : Nat := m - (index.val % m) - 1

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

attribute [local irreducible] numeratorReset controlledReset controlledBody
  pointArithmetic pointBody

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.MeasuredUncompute.NumeratorMeasurement
open QuantumAlg.MeasuredUncompute.NumeratorObservation

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private lemma numeratorMeasured_density (width : Nat) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    (ExecutionState.filterClassical
      ((Circuit.measurementSequence (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts width)).execute environment Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      ZMeasurement.branch
        (fun entry : ((context width).register.prod Reference).Index => word width entry.1)
        (NumeratorReset.outcome (stored.read (input width))) state.quantumMarginal := by
  let writes (original : Store (context width)) (basis : (context width).register.Index) :=
    Circuit.writeMeasurementPath (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts width) original
      (Circuit.measurementBasisPath (allowAllocation := false) (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts width) basis)
  have written_word (original : Store (context width))
      (basis : (context width).register.Index) :
      NumeratorReset.outcome ((writes original basis).read (input width)) = word width basis := by
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    rw [NumeratorReset.outcome_bit]
    exact (QubitReadouts.written_mask (allowAllocation := false) (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (services := .empty)
      (wire width) (wire_dimension width) (cell width) (cells_distinct width)
      original basis index).trans
        ((wire_basis_bit width basis index).trans (word_bit width basis index))
  have writes_iff (original : Store (context width))
      (basis : (context width).register.Index) :
      writes original basis = stored ↔
        word width basis = NumeratorReset.outcome (stored.read (input width)) := by
    constructor
    · intro same
      exact (written_word original basis).symm.trans
        (congrArg (fun result : Store (context width) =>
          NumeratorReset.outcome (result.read (input width))) same)
    · intro same
      exact NumeratorStoredFibers.outcome_injective width
        ((written_word original basis).trans same)
  apply DensityOperator.ext
  ext ⟨left, leftRef⟩ ⟨right, rightRef⟩
  rw [Circuit.measurementSequence_store_matrix_entry, ZMeasurement.branch_matrix]
  have weights :
      (fun original : Store (context width) × (ClassicalOracleModel.empty.HiddenState × History) =>
        if Circuit.writeMeasurementPath (allowAllocation := false) (gates := AlgorithmGate.model)
          (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
          (readouts width) original.1
          (Circuit.measurementBasisPath (allowAllocation := false) (gates := AlgorithmGate.model)
            (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
            (readouts width) left) = stored then (1 : ℂ) else 0) =
        fun _ => if word width left = NumeratorReset.outcome (stored.read (input width))
          then (1 : ℂ) else 0 := by
    funext original
    exact if_congr (writes_iff original.1 left) rfl rfl
  have constant (value : ℂ) :
      ExecutionState.weightedMatrixEntry state (fun _ => value)
        (left, leftRef) (right, rightRef) =
        value * state.quantumMarginal.matrix (left, leftRef) (right, rightRef) := by
    simp only [ExecutionState.weightedMatrixEntry, ExecutionState.quantumMarginal,
      Matrix.sum_apply, Finset.mul_sum]
  rw [weights, constant]
  have agree := measurement_agrees width left right
  by_cases same : word width left = word width right
  · rw [if_pos (agree.mpr same)]
    by_cases first : word width left = NumeratorReset.outcome (stored.read (input width))
    · rw [if_pos first, if_pos ⟨first, same.symm.trans first⟩, one_mul]
    · rw [if_neg first, if_neg (fun both => first both.1), zero_mul]
  · rw [if_neg (fun actual => same (agree.mp actual)),
      if_neg (fun both => same (both.1.trans both.2.symm))]

lemma numeratorReset_matrix (width : Nat) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    (ExecutionState.filterClassical ((numeratorReset width).execute environment Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      NumeratorResetConjugation.operator environment.quantum width Reference stored *
        (NumeratorStoredProjection.source width state stored).matrix *
        (NumeratorResetConjugation.operator environment.quantum width Reference
          stored).conjTranspose := by
  let hadamard : Circuit (.quantum AlgorithmGate.model .empty)
      (context width) (context width) false :=
    .unitary (NumeratorRuntime.program width (NumeratorReset.hadamardMember width))
  let prepared : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × (History × hadamard.Path)) :=
    hadamard.execute environment Reference state
  have measured := numeratorMeasured_density (environment := environment) width prepared stored
  have preparedMarginal : prepared.quantumMarginal =
      DensityOperator.applyUnitary
        (UnitaryOperator.prodTensor
          ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix
            environment.quantum)
          (1 : UnitaryOperator Reference)) state.quantumMarginal :=
    Circuit.unitary_jointDensity (environment := environment) (allowAllocation := false)
      (operations := .empty) (services := .empty)
      (NumeratorRuntime.program width (NumeratorReset.hadamardMember width)) state
  rw [NumeratorStoredFibers.source_eq_marginal]
  unfold numeratorReset
  rw [Circuit.seq_store_marginal (environment := environment), Circuit.seq_store_marginal
    (environment := environment),
    Circuit.selectedUnitary_store_matrix (allowAllocation := false)]
  refine (congrArg (fun density : DensityOperator ((context width).register.prod Reference) =>
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor
        ((NumeratorRuntime.program width
          (NumeratorReset.member width (stored.read (input width)))).matrix environment.quantum)
        (1 : UnitaryOperator Reference)) density).matrix) measured).trans ?_
  rw [preparedMarginal]
  simp only [DensityOperator.applyUnitary_matrix, ZMeasurement.branch,
    NumeratorResetConjugation.operator, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

attribute [local irreducible] numeratorReset controlledReset controlledBody
  pointArithmetic pointBody

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private lemma split_quantum_marginal
    {child caller : RuntimeCtx .quantum} (placement : ContextEmbedding child caller)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State caller Reference History) :
    (placement.split state).quantumMarginal =
      state.quantumMarginal.reindex (placement.referenceBasis Reference) := by
  rw [ContextEmbedding.split, InPlaceControlled.reindex_marginal,
    ExecutionState.mapClassical_quantumMarginal]

private lemma embedded_store_matrix_of_subsingleton_frame
    {child caller : RuntimeCtx .quantum} (placement : ContextEmbedding child caller)
    [Subsingleton (Store placement.frame)]
    (code : Circuit (.quantum AlgorithmGate.model .empty) child child false)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State caller Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store caller) :
    (((@Circuit.embed (.quantum AlgorithmGate.model .empty) child caller false
      placement code).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      (((code.execute environment (placement.frame.register.prod Reference)
        ((placement.split state).mapHistory (fun history =>
          (history.2.1, (history.1, history.2.2))))).filterClassical
        (fun entry => entry.1 = (placement.store stored).1)).quantumMarginal.matrix).submatrix
          (placement.referenceBasis Reference) (placement.referenceBasis Reference) := by
  let inputHistory : Store placement.frame × (ClassicalOracleModel.empty.HiddenState × History) →
      ClassicalOracleModel.empty.HiddenState × (Store placement.frame × History) :=
    fun history => (history.2.1, (history.1, history.2.2))
  let localState := (placement.split state).mapHistory inputHistory
  let localResult : State (child)
      (placement.frame.register.prod Reference)
      (ClassicalOracleModel.empty.HiddenState ×
        ((Store placement.frame × History) × code.Path)) :=
    code.execute environment (placement.frame.register.prod Reference) localState
  let restoreHistory :
      ClassicalOracleModel.empty.HiddenState ×
        ((Store placement.frame × History) × code.Path) →
      Store placement.frame ×
        (ClassicalOracleModel.empty.HiddenState × (History × code.Path)) :=
    fun history => (history.2.1.1, (history.1, (history.2.1.2, history.2.2)))
  have outputSame :
      (code.execute environment (placement.frame.register.prod Reference)
        localState).mapClassical (fun record =>
          (record.1, (record.2.2.1.1, (record.2.1, (record.2.2.1.2, record.2.2.2))))) =
        localResult.mapHistory restoreHistory := by
    dsimp only [localResult, State.mapHistory]
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  let output :=
    (@Circuit.embed (.quantum AlgorithmGate.model .empty) child caller false
      placement code).execute environment Reference state
  have executed : output =
      placement.join (localResult.mapHistory restoreHistory) := by
    have full := Circuit.circuit_execute_embed (environment := environment) (allowAllocation :=
      false)
      placement code Reference state
    refine full.trans (congrArg placement.join ?_)
    refine (ExecutionState.executionState_mapClassical_congr
      (second := inferInstanceAs (DecidableEq (Store (child) ×
        (Store placement.frame ×
          (ClassicalOracleModel.empty.HiddenState × (History × code.Path))))))
      _ rfl).trans ?_
    refine (congrArg (fun input : State (child)
        (placement.frame.register.prod Reference)
        (ClassicalOracleModel.empty.HiddenState × (Store placement.frame × History)) =>
      (code.execute environment (placement.frame.register.prod Reference) input).mapClassical
        (fun record =>
          (record.1, (record.2.2.1.1, (record.2.1, (record.2.2.1.2, record.2.2.2))))))
      ?_).trans outputSame
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  let coordinates := placement.referenceBasis Reference
  have joined :
      (((@Circuit.embed (.quantum AlgorithmGate.model .empty) child caller false
      placement code).execute environment Reference state).filterClassical
        (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ((localResult.filterClassical
        (fun entry => entry.1 = (placement.store stored).1)).quantumMarginal.matrix).submatrix
          coordinates coordinates := by
    have outputMatrix := congrArg (fun result : State (caller) Reference
        (ClassicalOracleModel.empty.HiddenState × (History × code.Path)) =>
      (result.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix) executed
    have joinedMatrix := join_store_matrix_of_subsingleton_frame placement
      (localResult.mapHistory restoreHistory) stored
    have historyMatrix := congrArg (fun density : DensityOperator
        ((child).register.prod
          (placement.frame.register.prod Reference)) =>
      density.matrix.submatrix coordinates coordinates)
      (State.mapHistory_store_marginal localResult restoreHistory ((placement.store stored).1))
    exact outputMatrix.trans (joinedMatrix.trans historyMatrix)
  exact joined

lemma controlledReset_matrix (width : Nat) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (InPlaceControlled.context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (InPlaceControlled.context width)) :
    (((controlledReset width).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      InPlaceControlled.framedResetOperator environment.quantum width Reference stored *
        state.quantumMarginal.matrix *
        (InPlaceControlled.framedResetOperator environment.quantum width Reference
          stored).conjTranspose := by
  unfold controlledReset
  let placement := ContextEmbedding.alongUnion (NumeratorMeasurement.context width)
    (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width)
  let reset : Circuit (.quantum AlgorithmGate.model .empty)
      (InPlaceControlled.context width)
      (InPlaceControlled.context width) false :=
    .embed placement (numeratorReset width)
  let : Subsingleton (Store placement.frame) := InPlaceControlled.controlStoreSubsingleton width
  let inputHistory : Store placement.frame × (ClassicalOracleModel.empty.HiddenState × History) →
      ClassicalOracleModel.empty.HiddenState × (Store placement.frame × History) :=
    fun history => (history.2.1, (history.1, history.2.2))
  let localState := (placement.split state).mapHistory inputHistory
  let localResult : State (NumeratorMeasurement.context width)
      (placement.frame.register.prod Reference)
      (ClassicalOracleModel.empty.HiddenState ×
        ((Store placement.frame × History) × (numeratorReset width).Path)) :=
    (numeratorReset width).execute environment (placement.frame.register.prod Reference) localState
  let coordinates := placement.referenceBasis Reference
  have joined :
      (((reset).execute environment Reference state).filterClassical
        (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ((localResult.filterClassical
        (fun entry => entry.1 = (placement.store stored).1)).quantumMarginal.matrix).submatrix
          coordinates coordinates :=
    embedded_store_matrix_of_subsingleton_frame placement
      (numeratorReset width) state stored
  have inverse :
      ((((reset).execute environment Reference state).filterClassical
        (fun entry => entry.1 = stored)).quantumMarginal.matrix).submatrix
          coordinates.symm coordinates.symm =
        (localResult.filterClassical
          (fun entry => entry.1 = (placement.store stored).1)).quantumMarginal.matrix := by
    rw [joined]
    ext row column
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  have localMarginal : localState.quantumMarginal =
      state.quantumMarginal.reindex coordinates :=
    (State.mapHistory_quantumMarginal (placement.split state) inputHistory).trans
      (split_quantum_marginal placement state)
  have actual := numeratorReset_matrix (environment := environment) width localState
    ((placement.store stored).1)
  rw [NumeratorStoredFibers.source_eq_marginal, localMarginal] at actual
  have transported := InPlaceControlled.pullback_conjugation coordinates
    state.quantumMarginal.matrix
    (((reset).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix
    (NumeratorResetConjugation.operator environment.quantum width (placement.frame.register.prod
      Reference)
      ((placement.store stored).1)) (inverse.trans actual)
  have coordinatesSame : coordinates =
      ContextUnion.referenceBasis (NumeratorMeasurement.context width)
        (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width)
        Reference :=
    alongUnion_referenceBasis _ _ _ Reference
  have storedSame : (placement.store stored).1 = InPlaceControlled.storeCoordinates width stored :=
    congrArg (fun stores => (stores stored).1) (alongUnion_store _ _ _)
  rw [coordinatesSame, storedSame] at transported
  exact transported

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

attribute [local irreducible] numeratorReset controlledReset controlledBody
  pointArithmetic pointBody

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private lemma controlledNative_marginal (width : Nat) (Reference : Register)
    (native : InPlaceControlled.NativeCircuit width) {History : Type} [Fintype History]
    (state : State (InPlaceControlled.context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((controlledNative width native).execute environment Reference state).quantumMarginal =
      DensityOperator.applyUnitary (InPlaceControlled.nativeJoint environment.quantum width
        Reference native)
        state.quantumMarginal := by
  exact Circuit.unitary_jointDensity (environment := environment) (allowAllocation := false)
    (operations := .empty) (services := .empty)
    (InPlaceControlled.runtimeProgram width native) state

lemma controlledBody_matrix (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) {Reference : Register} {History : Type} [Fintype History]
    (state : State (InPlaceControlled.context modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (InPlaceControlled.context modulus.size)) :
    (((controlledBody operation modulus prime).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      InPlaceControlled.actualOperator environment.quantum operation modulus prime Reference
        stored *
        state.quantumMarginal.matrix *
          (InPlaceControlled.actualOperator environment.quantum operation modulus prime Reference
            stored).conjTranspose := by
  unfold controlledBody
  let prefixCode := controlledNative modulus.size
    (InPlaceControlled.beforeReset operation modulus prime)
  let measured := controlledReset modulus.size
  let selected : Circuit (.quantum AlgorithmGate.model .empty)
      (InPlaceControlled.context modulus.size) (InPlaceControlled.context modulus.size) false :=
    .branch (InPlaceControlled.resultInput modulus.size) (fun value =>
      controlledNative modulus.size (InPlaceControlled.suffix operation modulus prime value))
  have first := Circuit.seq_store_marginal (environment := environment) prefixCode (.seq measured
    selected) state stored
  refine (congrArg DensityOperator.matrix first).trans ?_
  have second := Circuit.seq_store_marginal (environment := environment) measured selected
    (prefixCode.execute environment Reference state) stored
  refine (congrArg DensityOperator.matrix second).trans ?_
  refine (Circuit.selectedUnitary_store_matrix (allowAllocation := false)
    (InPlaceControlled.resultInput modulus.size)
    (fun value => InPlaceControlled.runtimeProgram modulus.size
      (InPlaceControlled.suffix operation modulus prime value)) environment
    (measured.execute environment Reference (prefixCode.execute environment Reference state))
      stored).trans ?_
  dsimp only [measured, prefixCode]
  have measuredBlock := controlledReset_matrix (environment := environment) modulus.size
    ((controlledNative modulus.size
      (InPlaceControlled.beforeReset operation modulus prime)).execute environment Reference
        state) stored
  rw [DensityOperator.applyUnitary_matrix]
  erw [measuredBlock, controlledNative_marginal, DensityOperator.applyUnitary_matrix]
  simp only [InPlaceControlled.actualOperator, InPlaceControlled.nativeJoint,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma pointArithmetic_store_matrix (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) {Reference : Register} {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.context modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (MeasuredPointAddition.context modulus.size)) :
    (((pointArithmetic operation modulus prime).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      Recovery.Point.Instrument.arithmeticOperator (environment := environment) operation modulus
        prime Reference stored *
        state.quantumMarginal.matrix *
          (Recovery.Point.Instrument.arithmeticOperator (environment := environment) operation
            modulus prime Reference
            stored).conjTranspose := by
  unfold pointArithmetic
  let placement := ContextEmbedding.alongUnion (InPlaceControlled.context modulus.size)
    (MeasuredPointAddition.selectorContext modulus.size)
    (MeasuredPointAddition.selector_disjoint modulus.size)
  let arithmetic : Circuit (.quantum AlgorithmGate.model .empty)
      (MeasuredPointAddition.context modulus.size)
      (MeasuredPointAddition.context modulus.size) false :=
    .embed placement (controlledBody operation modulus prime)
  let : Subsingleton (Store placement.frame) :=
    Recovery.Point.Instrument.selectorStoreSubsingleton modulus.size
  let inputHistory : Store placement.frame × (ClassicalOracleModel.empty.HiddenState × History) →
      ClassicalOracleModel.empty.HiddenState × (Store placement.frame × History) :=
    fun history => (history.2.1, (history.1, history.2.2))
  let localState := (placement.split state).mapHistory inputHistory
  let localResult : State (InPlaceControlled.context modulus.size)
      (placement.frame.register.prod Reference)
      (ClassicalOracleModel.empty.HiddenState ×
        ((Store placement.frame × History) × (controlledBody operation modulus prime).Path)) :=
    (controlledBody operation modulus prime).execute environment (placement.frame.register.prod
      Reference) localState
  let coordinates := placement.referenceBasis Reference
  have joined :
      (((arithmetic).execute environment Reference state).filterClassical
        (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ((localResult.filterClassical
        (fun entry => entry.1 = (placement.store stored).1)).quantumMarginal.matrix).submatrix
          coordinates coordinates :=
    embedded_store_matrix_of_subsingleton_frame placement
      (controlledBody operation modulus prime) state stored
  have inverse :
      ((((arithmetic).execute environment Reference state).filterClassical
        (fun entry => entry.1 = stored)).quantumMarginal.matrix).submatrix
          coordinates.symm coordinates.symm =
        (localResult.filterClassical
          (fun entry => entry.1 = (placement.store stored).1)).quantumMarginal.matrix := by
    rw [joined]
    ext row column
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  have localMarginal : localState.quantumMarginal =
      state.quantumMarginal.reindex coordinates :=
    (State.mapHistory_quantumMarginal (placement.split state) inputHistory).trans
      (split_quantum_marginal placement state)
  have actual := controlledBody_matrix (environment := environment) operation modulus prime
    localState
    ((placement.store stored).1)
  rw [localMarginal] at actual
  have transported := InPlaceControlled.pullback_conjugation coordinates
    state.quantumMarginal.matrix
    (((arithmetic).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix
    (InPlaceControlled.actualOperator environment.quantum operation modulus prime
      (placement.frame.register.prod Reference) ((placement.store stored).1))
    (inverse.trans actual)
  have coordinatesSame : coordinates =
      ContextUnion.referenceBasis (InPlaceControlled.context modulus.size)
        (MeasuredPointAddition.selectorContext modulus.size)
        (MeasuredPointAddition.selector_disjoint modulus.size) Reference :=
    alongUnion_referenceBasis _ _ _ Reference
  have storedSame : (placement.store stored).1 =
      Recovery.Point.Instrument.storeCoordinates modulus.size stored :=
    congrArg (fun stores => (stores stored).1) (alongUnion_store _ _ _)
  rw [coordinatesSame, storedSame] at transported
  exact transported

lemma pointArithmetic_marginal_matrix (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) {Reference : Register} {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.context modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((pointArithmetic operation modulus prime).execute environment Reference
      state).quantumMarginal.matrix =
      ∑ stored : Store (MeasuredPointAddition.context modulus.size),
        Recovery.Point.Instrument.arithmeticOperator (environment := environment) operation
          modulus prime Reference stored *
          state.quantumMarginal.matrix *
            (Recovery.Point.Instrument.arithmeticOperator (environment := environment) operation
              modulus prime Reference
              stored).conjTranspose := by
  rw [← Execution.sum_store_matrices
    ((pointArithmetic operation modulus prime).execute environment Reference state)]
  apply Finset.sum_congr rfl
  intro stored _
  exact pointArithmetic_store_matrix operation modulus prime state stored

private lemma pointNative_marginal (width : Nat) (Reference : Register)
    (native : MeasuredPointAddition.NativeCircuit width) {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((pointNative width native).execute environment Reference state).quantumMarginal =
      DensityOperator.applyUnitary (MeasuredPointAddition.nativeJoint (environment := environment)
        width Reference native)
        state.quantumMarginal := by
  exact Circuit.unitary_jointDensity (environment := environment) (allowAllocation := false)
    (operations := .empty) (services := .empty)
    (MeasuredPointAddition.runtimeProgram width native) state

lemma pointBody_store_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {Reference : Register} {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (finalStore : Store (MeasuredPointAddition.context p.size)) :
    (((pointBody E Q).execute environment Reference state).filterClassical
      (fun entry => entry.1 = finalStore)).quantumMarginal.matrix =
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
          divisionStore finalStore *
          state.quantumMarginal.matrix *
            (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
              divisionStore
              finalStore).conjTranspose := by
  unfold pointBody
  let before := pointNative p.size (MeasuredPointAddition.beforeDivision Q)
  let divided := pointArithmetic .division p Fact.out
  let middle := pointNative p.size (MeasuredPointAddition.beforeMultiplication Q)
  let multiplied := pointArithmetic .multiplication p Fact.out
  let after := pointNative p.size (MeasuredPointAddition.afterMultiplication E Q)
  let beforeState := before.execute environment Reference state
  let dividedState := divided.execute environment Reference beforeState
  let middleState := middle.execute environment Reference dividedState
  let multipliedState := multiplied.execute environment Reference middleState
  have first := Circuit.seq_store_marginal (environment := environment) before
    (.seq divided (.seq middle (.seq multiplied after))) state finalStore
  refine (congrArg DensityOperator.matrix first).trans ?_
  have second := Circuit.seq_store_marginal (environment := environment) divided (.seq middle (.seq
    multiplied after))
    beforeState finalStore
  refine (congrArg DensityOperator.matrix second).trans ?_
  have third := Circuit.seq_store_marginal (environment := environment) middle (.seq multiplied
    after)
    dividedState finalStore
  refine (congrArg DensityOperator.matrix third).trans ?_
  have fourth := Circuit.seq_store_marginal (environment := environment) multiplied after
    middleState finalStore
  refine (congrArg DensityOperator.matrix fourth).trans ?_
  have terminalMatrix :
      ((after.execute environment Reference multipliedState).filterClassical
        (fun entry => entry.1 = finalStore)).quantumMarginal.matrix =
      (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
        (MeasuredPointAddition.afterMultiplication E Q) : HilbertOperator
          ((MeasuredPointAddition.context p.size).register.prod Reference)) *
        (multipliedState.filterClassical
          (fun entry => entry.1 = finalStore)).quantumMarginal.matrix *
        (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
          (MeasuredPointAddition.afterMultiplication E Q) : HilbertOperator
            ((MeasuredPointAddition.context p.size).register.prod Reference)).conjTranspose := by
    exact (congrArg DensityOperator.matrix
      (Circuit.unitary_store_filter (environment := environment) (allowAllocation := false)
        (operations := .empty) (services := .empty)
        (MeasuredPointAddition.runtimeProgram p.size
          (MeasuredPointAddition.afterMultiplication E Q)) multipliedState
        (fun stored => stored = finalStore))).trans
      (DensityOperator.applyUnitary_matrix
        (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
          (MeasuredPointAddition.afterMultiplication E Q))
        (multipliedState.filterClassical (fun entry => entry.1 = finalStore)).quantumMarginal)
  refine terminalMatrix.trans ?_
  have multiplicationMatrix :
      (multipliedState.filterClassical
        (fun entry => entry.1 = finalStore)).quantumMarginal.matrix =
      Recovery.Point.Instrument.arithmeticOperator (environment := environment) .multiplication p
        Fact.out Reference finalStore *
        middleState.quantumMarginal.matrix *
        (Recovery.Point.Instrument.arithmeticOperator (environment := environment) .multiplication
          p Fact.out Reference
          finalStore).conjTranspose :=
    pointArithmetic_store_matrix .multiplication p Fact.out middleState finalStore
  have middleMatrix : middleState.quantumMarginal.matrix =
      (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
        (MeasuredPointAddition.beforeMultiplication Q) : HilbertOperator
          ((MeasuredPointAddition.context p.size).register.prod Reference)) *
        dividedState.quantumMarginal.matrix *
        (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
          (MeasuredPointAddition.beforeMultiplication Q) : HilbertOperator
            ((MeasuredPointAddition.context p.size).register.prod Reference)).conjTranspose := by
    exact (congrArg DensityOperator.matrix
      (pointNative_marginal p.size Reference (MeasuredPointAddition.beforeMultiplication Q)
        dividedState)).trans
      (DensityOperator.applyUnitary_matrix
        (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
          (MeasuredPointAddition.beforeMultiplication Q)) dividedState.quantumMarginal)
  have divisionMatrix : dividedState.quantumMarginal.matrix =
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        Recovery.Point.Instrument.arithmeticOperator (environment := environment) .division p
          Fact.out Reference divisionStore *
          beforeState.quantumMarginal.matrix *
          (Recovery.Point.Instrument.arithmeticOperator (environment := environment) .division p
            Fact.out Reference
            divisionStore).conjTranspose :=
    pointArithmetic_marginal_matrix .division p Fact.out beforeState
  have beforeMatrix : beforeState.quantumMarginal.matrix =
      (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
        (MeasuredPointAddition.beforeDivision Q) : HilbertOperator
          ((MeasuredPointAddition.context p.size).register.prod Reference)) *
        state.quantumMarginal.matrix *
        (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
          (MeasuredPointAddition.beforeDivision Q) : HilbertOperator
            ((MeasuredPointAddition.context p.size).register.prod Reference)).conjTranspose := by
    exact (congrArg DensityOperator.matrix
      (pointNative_marginal p.size Reference (MeasuredPointAddition.beforeDivision Q) state)).trans
      (DensityOperator.applyUnitary_matrix
        (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
          (MeasuredPointAddition.beforeDivision Q)) state.quantumMarginal)
  rw [multiplicationMatrix, middleMatrix, divisionMatrix, beforeMatrix]
  simp only [Recovery.Point.Instrument.pointKraus,
    Finset.mul_sum, Finset.sum_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

attribute [local irreducible] numeratorReset controlledReset controlledBody
  pointArithmetic pointBody

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

lemma pointBody_store_retained_fiber {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {Reference Tag : Register}
    {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × (History × Tag.Index)))
    (finalStore : Store (MeasuredPointAddition.context p.size)) (tag : Tag.Index) :
    (((pointBody E Q).execute environment Reference state).filterClassical
      (fun record => record.1 = finalStore ∧ record.2.2.1.2 = tag)).quantumMarginal.matrix =
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
          divisionStore finalStore *
          (state.filterClassical (fun record => record.2.2.2 = tag)).quantumMarginal.matrix *
          (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
            divisionStore
            finalStore).conjTranspose := by
  rw [(pointBody E Q).execute_encodedClassicalTag (Tag := Tag) environment state,
    decodeExecutionTag_store_fiber_matrix,
    pointBody_store_matrix E Q (Reference := Tag.prod Reference)
      (State.encodeOracleTag (Tag := Tag) state) finalStore]
  ext row column
  rw [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro divisionStore _
  have fixedTag := pointKraus_tag_conjugation (environment := environment) E Q Tag Reference
    divisionStore finalStore
    (State.encodeOracleTag (Tag := Tag) state).quantumMarginal.matrix tag
  rw [encodeOracleTag_fiber_matrix (Tag := Tag)] at fixedTag
  exact congrArg (fun matrix => matrix row column) fixedTag

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

attribute [local irreducible] numeratorReset controlledReset controlledBody
  pointArithmetic pointBody

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private lemma cells_map_filter_matrix {C D : Type} [Fintype C] [Fintype D]
    {R : Register} (state : ExecutionState C R) (labels : C → D) (predicate : D → Prop) :
    ((state.mapClassical labels).filterClassical predicate).quantumMarginal.matrix =
      (state.filterClassical (fun original =>
        predicate (labels original))).quantumMarginal.matrix := by
  ext row column
  rw [ExecutionState.filterClassical_matrix_weighted,
    ExecutionState.weightedMatrixEntry_mapClassical,
    ExecutionState.filterClassical_matrix_weighted]

private lemma cells_reindex_filter_matrix {C : Type} [Fintype C]
    {R S : Register} (state : ExecutionState C R) (basis : R.Index ≃ S.Index)
    (predicate : C → Prop) :
    ((state.reindex basis).filterClassical predicate).quantumMarginal.matrix =
      (state.filterClassical predicate).quantumMarginal.matrix.submatrix
        basis.symm basis.symm := by
  ext row column
  rw [ExecutionState.filterClassical_matrix_weighted, Matrix.submatrix_apply,
    ExecutionState.filterClassical_matrix_weighted]
  simp only [ExecutionState.weightedMatrixEntry, ExecutionState.reindex_block_entry]

private lemma cells_map_filter_matrix_decisions {C D : Type} [Fintype C] [Fintype D]
    {R : Register} (state : ExecutionState C R) (labels : C → D) (predicate : D → Prop)
    {mapDecision : DecidableEq D} {outputDecision : DecidablePred predicate}
    {inputDecision : DecidablePred (fun original => predicate (labels original))} :
    (@ExecutionState.filterClassical D _ R
      (@ExecutionState.mapClassical C D _ _ R mapDecision state labels)
      predicate outputDecision).quantumMarginal.matrix =
      (@ExecutionState.filterClassical C _ R state
        (fun original => predicate (labels original)) inputDecision).quantumMarginal.matrix := by
  cases Subsingleton.elim mapDecision (Classical.decEq D)
  cases Subsingleton.elim outputDecision
    (fun value => Classical.propDecidable (predicate value))
  cases Subsingleton.elim inputDecision
    (fun value => Classical.propDecidable (predicate (labels value)))
  exact cells_map_filter_matrix state labels predicate

private lemma cells_reindex_filter_matrix_decisions {C : Type} [Fintype C]
    {R S : Register} (state : ExecutionState C R) (basis : R.Index ≃ S.Index)
    (predicate : C → Prop)
    {outputDecision inputDecision : DecidablePred predicate} :
    (@ExecutionState.filterClassical C _ S (state.reindex basis)
      predicate outputDecision).quantumMarginal.matrix =
      (@ExecutionState.filterClassical C _ R
        state predicate inputDecision).quantumMarginal.matrix.submatrix basis.symm basis.symm := by
  cases Subsingleton.elim outputDecision
    (fun value => Classical.propDecidable (predicate value))
  cases Subsingleton.elim inputDecision
    (fun value => Classical.propDecidable (predicate value))
  exact cells_reindex_filter_matrix state basis predicate

private lemma cells_filter_matrix_predicate_congr {C : Type} [Fintype C]
    {R : Register} (state : ExecutionState C R) {first second : C → Prop}
    (same : first = second)
    {firstDecision : DecidablePred first} {secondDecision : DecidablePred second} :
    (@ExecutionState.filterClassical C _ R state first firstDecision).quantumMarginal.matrix =
      (@ExecutionState.filterClassical C _ R
        state second secondDecision).quantumMarginal.matrix := by
  cases same
  cases Subsingleton.elim firstDecision secondDecision
  rfl

private lemma cells_frame_history_input_swap {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {Reference : Register}
    {Hidden Frame History : Type} [Fintype Hidden] [Fintype Frame] [Fintype History]
    (state : State ctx Reference (Frame × (Hidden × History))) :
    State.mapHistory (ctx := ctx) (Reference := Reference)
      (H := Hidden × (Frame × History)) (K := Hidden × (History × Frame))
      (state.mapClassical (fun record =>
        (record.1, (record.2.2.1, (record.2.1, record.2.2.2)))))
      (fun record => (record.1, (record.2.2, record.2.1))) =
      state.mapClassical (fun record =>
        (record.1, (record.2.2.1, (record.2.2.2, record.2.1)))) := by
  dsimp only [State.mapHistory]
  refine (ExecutionState.executionState_mapClassical_comp_instances
    (result := Classical.decEq _) state _ _).trans ?_
  exact ExecutionState.executionState_mapClassical_congr state rfl

private lemma cells_frame_history_output_swap {kind : ProblemKind}
    {ctx : RuntimeCtx kind} {Reference : Register}
    {Hidden Frame History Path : Type} [Fintype Hidden] [Fintype Frame]
    [Fintype History] [Fintype Path]
    (state : State ctx Reference (Hidden × ((Frame × History) × Path))) :
    (state.mapHistory (fun record =>
      (record.1, ((record.2.1.2, record.2.1.1), record.2.2)))).mapClassical
        (fun record =>
          (record.1, (record.2.2.1.2, (record.2.1, (record.2.2.1.1, record.2.2.2))))) =
      state.mapClassical (fun record =>
        (record.1, (record.2.2.1.1, (record.2.1, (record.2.2.1.2, record.2.2.2))))) := by
  dsimp only [State.mapHistory]
  refine (ExecutionState.executionState_mapClassical_comp_instances
    (result := Classical.decEq _) state _ _).trans ?_
  exact ExecutionState.executionState_mapClassical_congr state rfl

private lemma cells_join_store_fiber
    {child caller : RuntimeCtx .quantum} (placement : ContextEmbedding child caller)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State child (placement.frame.register.prod Reference)
      (Store placement.frame × History)) (stored : Store caller) (predicate : History → Prop) :
    ((placement.join state).filterClassical
      (fun record => record.1 = stored ∧ predicate record.2)).quantumMarginal.matrix =
      Matrix.submatrix
        ((state.filterClassical (fun record => record.1 = (placement.store stored).1 ∧
          record.2.1 = (placement.store stored).2 ∧ predicate record.2.2)).quantumMarginal.matrix)
        (placement.referenceBasis Reference) (placement.referenceBasis Reference) := by
  let coordinates := placement.referenceBasis Reference
  let selected : Store caller × History → Prop :=
    fun record => record.1 = stored ∧ predicate record.2
  let mapped : ExecutionState (Store caller × History)
      (child.register.prod (placement.frame.register.prod Reference)) :=
    state.mapClassical (placement.record History).symm
  have joined : placement.join state = mapped.reindex coordinates.symm := by
    unfold ContextEmbedding.join
    exact congrArg (fun result : ExecutionState (Store caller × History)
        (child.register.prod (placement.frame.register.prod Reference)) =>
      result.reindex coordinates.symm)
      (ExecutionState.executionState_mapClassical_congr state rfl)
  refine (cells_filter_matrix_predicate_congr (placement.join state)
    (rfl : selected = selected)
    (secondDecision := fun _ => Classical.propDecidable _)).trans ?_
  refine (congrArg (fun result : ExecutionState (Store caller × History)
      (caller.register.prod Reference) =>
    (@ExecutionState.filterClassical _ _ _ result selected
      (fun _ => Classical.propDecidable _)).quantumMarginal.matrix) joined).trans ?_
  refine (cells_reindex_filter_matrix_decisions mapped coordinates.symm selected
    (outputDecision := fun _ => Classical.propDecidable _)
    (inputDecision := fun _ => Classical.propDecidable _)).trans ?_
  apply congrArg (fun matrix : HilbertOperator
      (child.register.prod (placement.frame.register.prod Reference)) =>
    matrix.submatrix coordinates coordinates)
  refine (cells_map_filter_matrix_decisions state (placement.record History).symm selected
    (mapDecision := inferInstance)
    (outputDecision := fun _ => Classical.propDecidable _)
    (inputDecision := fun _ => Classical.propDecidable _)).trans ?_
  have predicateSame :
      (fun record : Store child × (Store placement.frame × History) =>
        ((placement.record History).symm record).1 = stored ∧
          predicate ((placement.record History).symm record).2) =
        (fun record => record.1 = (placement.store stored).1 ∧
          record.2.1 = (placement.store stored).2 ∧ predicate record.2.2) := by
    funext record
    apply propext
    change (placement.store.symm (record.1, record.2.1) = stored ∧
      predicate record.2.2) ↔ _
    rw [Equiv.symm_apply_eq, Prod.ext_iff, and_assoc]
  exact cells_filter_matrix_predicate_congr state predicateSame
    (firstDecision := fun _ => Classical.propDecidable _)

private lemma cells_split_store_fiber
    {child caller : RuntimeCtx .quantum} (placement : ContextEmbedding child caller)
    (keep : Store child → Store child → Prop)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State caller Reference History) (stored : Store caller) (predicate : History → Prop) :
    ((placement.split state).filterClassical (fun record =>
      keep (placement.store stored).1 record.1 ∧ record.2.1 = (placement.store stored).2 ∧
        predicate record.2.2)).quantumMarginal.matrix =
      (state.filterClassical (fun record =>
        keep (placement.store stored).1 (placement.store record.1).1 ∧
          (placement.store record.1).2 = (placement.store stored).2 ∧
            predicate record.2)).quantumMarginal.matrix.submatrix
              (placement.referenceBasis Reference).symm
              (placement.referenceBasis Reference).symm := by
  let coordinates := placement.referenceBasis Reference
  let selected : Store child × (Store placement.frame × History) → Prop :=
    fun record => keep (placement.store stored).1 record.1 ∧
      record.2.1 = (placement.store stored).2 ∧ predicate record.2.2
  let mapped : ExecutionState (Store child × (Store placement.frame × History))
      (caller.register.prod Reference) := state.mapClassical (placement.record History)
  have split : placement.split state = mapped.reindex coordinates := by
    unfold ContextEmbedding.split
    exact congrArg (fun result : ExecutionState
        (Store child × (Store placement.frame × History)) (caller.register.prod Reference) =>
      result.reindex coordinates)
      (ExecutionState.executionState_mapClassical_congr state rfl)
  refine (cells_filter_matrix_predicate_congr (placement.split state)
    (rfl : selected = selected)
    (secondDecision := fun _ => Classical.propDecidable _)).trans ?_
  refine (congrArg (fun result : ExecutionState
      (Store child × (Store placement.frame × History))
      (child.register.prod (placement.frame.register.prod Reference)) =>
    (@ExecutionState.filterClassical _ _ _ result selected
      (fun _ => Classical.propDecidable _)).quantumMarginal.matrix) split).trans ?_
  refine (cells_reindex_filter_matrix_decisions mapped coordinates selected
    (outputDecision := fun _ => Classical.propDecidable _)
    (inputDecision := fun _ => Classical.propDecidable _)).trans ?_
  apply congrArg (fun matrix : HilbertOperator (caller.register.prod Reference) =>
    matrix.submatrix coordinates.symm coordinates.symm)
  refine (cells_map_filter_matrix_decisions state (placement.record History) selected
    (mapDecision := inferInstance)
    (outputDecision := fun _ => Classical.propDecidable _)
    (inputDecision := fun _ => Classical.propDecidable _)).trans ?_
  exact cells_filter_matrix_predicate_congr state rfl
    (firstDecision := fun _ => Classical.propDecidable _)

private lemma cells_local_frame_matrix
    {C Hidden Frame History Path Outcome : Type} [Fintype C] [Fintype Hidden]
    [Fintype Frame] [Fintype History] [Fintype Path] [Fintype Outcome] {R : Register}
    (input : ExecutionState (C × (Hidden × (History × Frame))) R)
    (output : ExecutionState (C × (Hidden × ((History × Frame) × Path))) R)
    (operators : Outcome → HilbertOperator R) (keep : C → C → Prop) (stored : C)
    (law : ∀ selected : History × Frame → Prop,
      (output.filterClassical (fun record =>
        record.1 = stored ∧ selected record.2.2.1)).quantumMarginal.matrix =
        ∑ outcome, operators outcome *
          (input.filterClassical (fun record =>
            keep stored record.1 ∧ selected record.2.2)).quantumMarginal.matrix *
              (operators outcome).conjTranspose)
    (frame : Frame) (predicate : History → Prop) :
    (output.filterClassical (fun record => record.1 = stored ∧
      record.2.2.1.2 = frame ∧ predicate record.2.2.1.1)).quantumMarginal.matrix =
      ∑ outcome, operators outcome *
        (input.filterClassical (fun record => keep stored record.1 ∧
          record.2.2.2 = frame ∧ predicate record.2.2.1)).quantumMarginal.matrix *
            (operators outcome).conjTranspose := by
  have original := law (fun history => history.2 = frame ∧ predicate history.1)
  refine Eq.trans ?_ (original.trans ?_)
  · exact cells_filter_matrix_predicate_congr output rfl
  · apply Finset.sum_congr rfl
    intro outcome _
    apply congrArg (fun matrix : HilbertOperator R =>
      operators outcome * matrix * (operators outcome).conjTranspose)
    exact cells_filter_matrix_predicate_congr input rfl
private lemma child_store_history_with_frame
    {child : RuntimeCtx .quantum}
    (code : Circuit (.quantum AlgorithmGate.model .empty) child child false)
    {Outcome : Type} [Fintype Outcome]
    (kernel : (Reference : Register) → Outcome → Store child →
      Matrix (child.register.prod Reference).Index (child.register.prod Reference).Index ℂ)
    (keep : Store child → Store child → Prop)
    (localLaw : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State child Reference (ClassicalOracleModel.empty.HiddenState × History))
      (stored : Store child) (predicate : History → Prop),
      ((code.execute environment Reference state).filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
        ∑ outcome : Outcome, kernel Reference outcome stored *
          (state.filterClassical (fun record =>
            keep stored record.1 ∧ predicate record.2.2)).quantumMarginal.matrix *
          (kernel Reference outcome stored).conjTranspose)
    {FrameStore History : Type} [Fintype FrameStore] [Fintype History] {Reference : Register}
    (inputState : State child Reference
      (ClassicalOracleModel.empty.HiddenState × (History × FrameStore)))
    (finalChild : Store child) (finalFrame : FrameStore) (predicate : History → Prop) :
    let localOutput : State child Reference
        (ClassicalOracleModel.empty.HiddenState × ((History × FrameStore) × code.Path)) :=
      code.execute environment Reference inputState
    (localOutput.filterClassical (fun record => record.1 = finalChild ∧
      record.2.2.1.2 = finalFrame ∧ predicate record.2.2.1.1)).quantumMarginal.matrix =
      ∑ outcome : Outcome, kernel Reference outcome finalChild *
        (inputState.filterClassical (fun record => keep finalChild record.1 ∧
          record.2.2.2 = finalFrame ∧ predicate record.2.2.1)).quantumMarginal.matrix *
        (kernel Reference outcome finalChild).conjTranspose := by
  let localOutput : State child Reference
      (ClassicalOracleModel.empty.HiddenState × ((History × FrameStore) × code.Path)) :=
    code.execute environment Reference inputState
  exact cells_local_frame_matrix
    (C := Store child) (Hidden := ClassicalOracleModel.empty.HiddenState)
    (Frame := FrameStore) (History := History) (Path := code.Path)
    (Outcome := Outcome) (R := child.register.prod Reference)
    inputState localOutput (fun outcome => kernel Reference outcome finalChild)
    keep finalChild
    (fun selected => by
      refine (cells_filter_matrix_predicate_congr
        (C := Store child × (ClassicalOracleModel.empty.HiddenState ×
          ((History × FrameStore) × code.Path)))
        (R := child.register.prod Reference) localOutput rfl).trans
        ((localLaw Reference (History := History × FrameStore)
          inputState finalChild selected).trans ?_)
      apply Finset.sum_congr rfl
      intro outcome _
      apply congrArg (fun matrix : HilbertOperator (child.register.prod Reference) =>
        kernel Reference outcome finalChild * matrix *
          (kernel Reference outcome finalChild).conjTranspose)
      exact cells_filter_matrix_predicate_congr
        (C := Store child ×
          (ClassicalOracleModel.empty.HiddenState × (History × FrameStore)))
        (R := child.register.prod Reference) inputState rfl)
    finalFrame predicate


private lemma cells_frame_history_execution_swap {model : ExecutionModel}
    {environment : model.Environment}
    {ctx : RuntimeCtx model.kind} (code : Circuit model ctx ctx false) (Reference : Register)
    {Frame History : Type} [Fintype Frame] [Fintype History]
    (actualInput : State ctx Reference (model.HiddenState × (Frame × History)))
    (taggedInput : State ctx Reference (model.HiddenState × (History × Frame)))
    (inputSame : actualInput.mapHistory
      (fun record => (record.1, (record.2.2, record.2.1))) = taggedInput) :
    ((code.execute environment Reference actualInput).mapClassical
      (fun record =>
        (record.1, (record.2.2.1.1, (record.2.1, (record.2.2.1.2, record.2.2.2)))))) =
      (code.execute environment Reference taggedInput).mapClassical
        (fun record =>
          (record.1, (record.2.2.1.2, (record.2.1, (record.2.2.1.1, record.2.2.2))))) := by
  have natural := Circuit.execute_mapHistory (environment := environment) (model := model) (pre :=
    ctx) (post := ctx)
    (allowAllocation := false) code Reference
    (H := Frame × History) (K := History × Frame)
    actualInput (fun record : Frame × History => (record.2, record.1))
  have executionSame : code.execute environment Reference taggedInput =
      (code.execute environment Reference actualInput).mapHistory
        (fun record => (record.1, ((record.2.1.2, record.2.1.1), record.2.2))) :=
    (congrArg (code.execute environment Reference) inputSame.symm).trans natural
  refine (cells_frame_history_output_swap (ctx := ctx) (Reference := Reference)
    (Hidden := model.HiddenState) (Frame := Frame) (History := History) (Path := code.Path)
    (code.execute environment Reference actualInput)).symm.trans ?_
  exact Circuit.pushforward_congr
    (C := Store ctx × (model.HiddenState × ((History × Frame) × code.Path)))
    (D := Store ctx × (Frame × (model.HiddenState × (History × code.Path))))
    (R := ctx.register.prod Reference) executionSame.symm
    (fun record =>
      (record.1, (record.2.2.1.2, (record.2.1, (record.2.2.1.1, record.2.2.2)))))


private lemma cells_embed_execute_tag_last {model : ExecutionModel}
    {environment : model.Environment}
    {child caller : RuntimeCtx model.kind} (placement : ContextEmbedding child caller)
    (code : Circuit model child child false) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State caller Reference (model.HiddenState × History)) :
    (Circuit.embed (allowAllocation := false) placement code).execute environment Reference state =
      placement.join
        ((code.execute environment (placement.frame.register.prod Reference)
          ((placement.split state).mapClassical (fun record =>
            (record.1, (record.2.2.1, (record.2.2.2, record.2.1)))))).mapClassical
          (fun record =>
            (record.1, (record.2.2.1.2,
              (record.2.1, (record.2.2.1.1, record.2.2.2)))))) := by
  let split := placement.split state
  let actualInput : State child (placement.frame.register.prod Reference)
      (model.HiddenState × (Store placement.frame × History)) :=
    split.mapClassical (fun record =>
      (record.1, (record.2.2.1, (record.2.1, record.2.2.2))))
  let taggedInput : State child (placement.frame.register.prod Reference)
      (model.HiddenState × (History × Store placement.frame)) :=
    split.mapClassical (fun record =>
      (record.1, (record.2.2.1, (record.2.2.2, record.2.1))))
  have inputSame : actualInput.mapHistory
      (fun record => (record.1, (record.2.2, record.2.1))) = taggedInput := by
    exact cells_frame_history_input_swap (ctx := child)
      (Reference := placement.frame.register.prod Reference) (Hidden := model.HiddenState)
      (Frame := Store placement.frame) (History := History) split
  have restored := cells_frame_history_execution_swap (environment := environment) (model :=
    model) (ctx := child)
    code (placement.frame.register.prod Reference)
    (Frame := Store placement.frame) (History := History) actualInput taggedInput inputSame
  refine (Circuit.circuit_execute_embed (environment := environment) (allowAllocation := false)
    placement code Reference state).trans (congrArg placement.join ?_)
  refine (ExecutionState.executionState_mapClassical_congr
    (second := inferInstanceAs (DecidableEq (Store child ×
      (Store placement.frame × (model.HiddenState × (History × code.Path)))))) _ rfl).trans ?_
  refine (congrArg (fun input : State child (placement.frame.register.prod Reference)
      (model.HiddenState × (Store placement.frame × History)) =>
    (code.execute environment (placement.frame.register.prod Reference) input).mapClassical
      (fun record =>
        (record.1, (record.2.2.1.1, (record.2.1, (record.2.2.1.2, record.2.2.2))))))
    ?_).trans restored
  exact ExecutionState.executionState_mapClassical_congr _ rfl

private lemma cells_pullback_sandwich {Caller Child : Type}
    [Fintype Caller] [Fintype Child] (basis : Caller ≃ Child)
    (operator : Matrix Child Child ℂ) (density : Matrix Caller Caller ℂ) :
    (operator * density.submatrix basis.symm basis.symm * operator.conjTranspose).submatrix
        basis basis =
      operator.submatrix basis basis * density *
        (operator.submatrix basis basis).conjTranspose := by
  have recovered : (density.submatrix basis.symm basis.symm).submatrix basis basis = density := by
    ext row column
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← Matrix.submatrix_mul_equiv (operator * density.submatrix basis.symm basis.symm)
      operator.conjTranspose basis basis basis,
    ← Matrix.submatrix_mul_equiv operator (density.submatrix basis.symm basis.symm)
      basis basis basis,
    recovered, ← Matrix.conjTranspose_submatrix]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

attribute [local irreducible] numeratorReset controlledReset controlledBody
  pointArithmetic pointBody

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

def indexedPointCall {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (readyContext p.size count) (readyContext p.size count) false :=
  .embed (indexedPointPlacement p.size active) (pointBody E Q)

def indexedPointCallWithCells {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {count : Nat} (active : Fin count) (cells : Nat) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (MeasurementCells.context (readyContext p.size count) 2 cells)
      (MeasurementCells.context (readyContext p.size count) 2 cells) false :=
  .embed (cellsPlacement (readyContext p.size count) 2 cells)
    (indexedPointCall E Q active)

def streamingPointCall {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m)) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (MeasurementCells.context (readyContext p.size 2) 2 (2 * m))
      (MeasurementCells.context (readyContext p.size 2) 2 (2 * m)) false :=
  indexedPointCallWithCells E (points index) (0 : Fin 2) (2 * m)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

attribute [local irreducible] numeratorReset controlledReset controlledBody
  pointArithmetic pointBody

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private def historyPredicateTag : Register where
  Index := Bool
  fintype := inferInstance
  decEq := inferInstance

private lemma pointBody_store_history_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (MeasuredPointAddition.context p.size)) (predicate : History → Prop) :
    (((pointBody E Q).execute environment Reference state).filterClassical
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
          divisionStore stored *
          (state.filterClassical (fun record => predicate record.2.2)).quantumMarginal.matrix *
          (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
            divisionStore
            stored).conjTranspose := by
  have actual := (pointBody E Q).execute_mapHistory environment Reference state
    (fun history => (history, decide (predicate history)))
  have selected := pointBody_store_retained_fiber (environment := environment) E Q (Tag :=
    historyPredicateTag)
    (state.mapHistory (fun record =>
      (record.1, (record.2, decide (predicate record.2))))) stored (true : Bool)
  have observed := congrArg (fun result : State (MeasuredPointAddition.context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × ((History × Bool) × (pointBody E Q).Path)) =>
    (result.filterClassical (fun record =>
      record.1 = stored ∧ record.2.2.1.2 = true)).quantumMarginal.matrix) actual
  have selectedMatrix := observed.symm.trans selected
  dsimp only [State.mapHistory] at selectedMatrix
  have outputPredicate :
      (fun record : Store (MeasuredPointAddition.context p.size) ×
          (ClassicalOracleModel.empty.HiddenState × (History × (pointBody E Q).Path)) =>
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
      ((pointBody E Q).execute environment Reference state) outputPredicate.symm
      (secondDecision := fun _ => Classical.propDecidable _)).trans ?_
    exact (cells_map_filter_matrix_decisions ((pointBody E Q).execute environment Reference state)
      (fun record => (record.1,
        (record.2.1, ((record.2.2.1, decide (predicate record.2.2.1)), record.2.2.2))))
      (fun record => record.1 = stored ∧ record.2.2.1.2 = true)
      (inputDecision := fun _ => Classical.propDecidable _)).symm
  · apply Finset.sum_congr rfl
    intro divisionStore _
    apply congrArg (fun matrix : HilbertOperator
        ((MeasuredPointAddition.context p.size).register.prod Reference) =>
      Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
        divisionStore stored * matrix *
        (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
          divisionStore stored).conjTranspose)
    exact (cells_map_filter_matrix_decisions state
      (fun record => (record.1, (record.2.1, (record.2.2, decide (predicate record.2.2)))))
      (fun record => record.2.2.2 = true)
      (inputDecision := fun _ => Classical.propDecidable _)).trans
        (cells_filter_matrix_predicate_congr state inputPredicate
          (firstDecision := fun _ => Classical.propDecidable _))

private lemma embed_output_store_history_matrix
    {child caller : RuntimeCtx .quantum} (placement : ContextEmbedding child caller)
    {Reference : Register} {History Path : Type} [Fintype History] [Fintype Path]
    (localOutput : State child (placement.frame.register.prod Reference)
      (ClassicalOracleModel.empty.HiddenState × ((History × Store placement.frame) × Path)))
    (stored : Store caller) (predicate : History → Prop) :
    let coordinates := placement.referenceBasis Reference
    let finalChild := (placement.store stored).1
    let finalFrame := (placement.store stored).2
    let restore := fun record : Store child ×
        (ClassicalOracleModel.empty.HiddenState ×
          ((History × Store placement.frame) × Path)) =>
      (record.1, (record.2.2.1.2, (record.2.1, (record.2.2.1.1, record.2.2.2))))
    ((placement.join (localOutput.mapClassical restore)).filterClassical
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      (localOutput.filterClassical (fun record => record.1 = finalChild ∧
        record.2.2.1.2 = finalFrame ∧ predicate record.2.2.1.1)).quantumMarginal.matrix.submatrix
          coordinates coordinates := by
  let coordinates := placement.referenceBasis Reference
  let finalChild := (placement.store stored).1
  let finalFrame := (placement.store stored).2
  let restore := fun record : Store child ×
      (ClassicalOracleModel.empty.HiddenState ×
        ((History × Store placement.frame) × Path)) =>
    (record.1, (record.2.2.1.2, (record.2.1, (record.2.2.1.1, record.2.2.2))))
  let restored : State child (placement.frame.register.prod Reference)
      (Store placement.frame ×
        (ClassicalOracleModel.empty.HiddenState × (History × Path))) :=
    localOutput.mapClassical restore
  have joined := cells_join_store_fiber placement (Reference := Reference)
    (History := ClassicalOracleModel.empty.HiddenState × (History × Path)) restored stored
    (fun history => predicate history.2.1)
  refine joined.trans ?_
  apply congrArg (fun matrix : HilbertOperator
      (child.register.prod (placement.frame.register.prod Reference)) =>
    matrix.submatrix coordinates coordinates)
  let selected : Store child × (Store placement.frame ×
      (ClassicalOracleModel.empty.HiddenState × (History × Path))) → Prop :=
    fun record => record.1 = finalChild ∧ record.2.1 = finalFrame ∧ predicate record.2.2.2.1
  refine (cells_filter_matrix_predicate_congr restored (rfl : selected = selected)
    (secondDecision := fun _ => Classical.propDecidable _)).trans ?_
  refine (cells_map_filter_matrix_decisions localOutput restore selected
    (mapDecision := inferInstance)
    (outputDecision := fun _ => Classical.propDecidable _)
    (inputDecision := fun _ => Classical.propDecidable _)).trans ?_
  exact cells_filter_matrix_predicate_congr localOutput rfl
    (firstDecision := fun _ => Classical.propDecidable _)

private lemma embed_input_store_history_matrix
    {child caller : RuntimeCtx .quantum} (placement : ContextEmbedding child caller)
    (keep : Store child → Store child → Prop)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State caller Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store caller) (predicate : History → Prop) :
    let coordinates := placement.referenceBasis Reference
    let finalChild := (placement.store stored).1
    let finalFrame := (placement.store stored).2
    let localInput : State child (placement.frame.register.prod Reference)
        (ClassicalOracleModel.empty.HiddenState × (History × Store placement.frame)) :=
      (placement.split state).mapClassical (fun record =>
        (record.1, (record.2.2.1, (record.2.2.2, record.2.1))))
    (localInput.filterClassical (fun record => keep finalChild record.1 ∧
      record.2.2.2 = finalFrame ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      (state.filterClassical (fun record =>
        keep finalChild (placement.store record.1).1 ∧
          (placement.store record.1).2 = finalFrame ∧
            predicate record.2.2)).quantumMarginal.matrix.submatrix
              coordinates.symm coordinates.symm := by
  let finalChild := (placement.store stored).1
  let finalFrame := (placement.store stored).2
  let localInput : State child (placement.frame.register.prod Reference)
      (ClassicalOracleModel.empty.HiddenState × (History × Store placement.frame)) :=
    (placement.split state).mapClassical (fun record =>
      (record.1, (record.2.2.1, (record.2.2.2, record.2.1))))
  let selected : Store child ×
      (ClassicalOracleModel.empty.HiddenState × (History × Store placement.frame)) → Prop :=
    fun record => keep finalChild record.1 ∧
      record.2.2.2 = finalFrame ∧ predicate record.2.2.1
  refine (cells_filter_matrix_predicate_congr localInput (rfl : selected = selected)
    (secondDecision := fun _ => Classical.propDecidable _)).trans ?_
  refine (cells_map_filter_matrix_decisions
    (C := Store child × (Store placement.frame ×
      (ClassicalOracleModel.empty.HiddenState × History)))
    (D := Store child ×
      (ClassicalOracleModel.empty.HiddenState × (History × Store placement.frame)))
    (R := child.register.prod (placement.frame.register.prod Reference))
    (placement.split state) (fun record =>
      (record.1, (record.2.2.1, (record.2.2.2, record.2.1)))) selected
    (mapDecision := inferInstance)
    (outputDecision := fun _ => Classical.propDecidable _)
    (inputDecision := fun _ => Classical.propDecidable _)).trans ?_
  exact (cells_filter_matrix_predicate_congr (placement.split state) rfl
    (firstDecision := fun _ => Classical.propDecidable _)).trans
    (cells_split_store_fiber placement keep (Reference := Reference)
      (History := ClassicalOracleModel.empty.HiddenState × History) state stored
      (fun history => predicate history.2))

private lemma cells_pullback_sum_sandwich {Caller Child Outcome : Type}
    [Fintype Caller] [Fintype Child] [Fintype Outcome]
    (coordinates : Caller ≃ Child) (operators : Outcome → Matrix Child Child ℂ)
    (density : Matrix Caller Caller ℂ) (localInput localOutput : Matrix Child Child ℂ)
    (inputFiber : localInput = density.submatrix coordinates.symm coordinates.symm)
    (localLaw : localOutput = ∑ outcome : Outcome,
      operators outcome * localInput * (operators outcome).conjTranspose) :
    localOutput.submatrix coordinates coordinates =
      ∑ outcome : Outcome, (operators outcome).submatrix coordinates coordinates * density *
        ((operators outcome).submatrix coordinates coordinates).conjTranspose := by
  rw [localLaw, inputFiber]
  ext row column
  rw [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro outcome _
  exact congrArg (fun matrix => matrix row column)
    (cells_pullback_sandwich coordinates (operators outcome) density)

private lemma cells_embed_filter_store_history_matrix
    {child caller : RuntimeCtx .quantum} (placement : ContextEmbedding child caller)
    (code : Circuit (.quantum AlgorithmGate.model .empty) child child false)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State caller Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store caller) (predicate : History → Prop) :
    let localInput := (placement.split state).mapClassical (fun record =>
      (record.1, (record.2.2.1, (record.2.2.2, record.2.1))))
    let localOutput := code.execute environment (placement.frame.register.prod Reference) localInput
    let restore := fun record : Store child × (ClassicalOracleModel.empty.HiddenState ×
        ((History × Store placement.frame) × code.Path)) =>
      (record.1, (record.2.2.1.2, (record.2.1, (record.2.2.1.1, record.2.2.2))))
    (((Circuit.embed (allowAllocation := false) placement code).execute
      environment Reference state).filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ((placement.join (localOutput.mapClassical restore)).filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix := by
  exact congrArg (fun result : State caller Reference
      (ClassicalOracleModel.empty.HiddenState × (History × code.Path)) =>
    (result.filterClassical (fun record =>
      record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix)
    (cells_embed_execute_tag_last placement code Reference state)

section

-- Compose the proved split/execute/join laws without normalizing their interpreters again.
attribute [local irreducible] Circuit.execute ContextEmbedding.split ContextEmbedding.join
attribute [local irreducible] Circuit.pathFintype
attribute [local irreducible] ExecutionState.filterClassical ExecutionState.quantumMarginal
  ExecutionState.mapClassical

private lemma embed_store_history_matrix
    {child caller : RuntimeCtx .quantum} (placement : ContextEmbedding child caller)
    (code : Circuit (.quantum AlgorithmGate.model .empty) child child false)
    {Outcome : Type} [Fintype Outcome]
    (kernel : (Reference : Register) → Outcome → Store child →
      Matrix (child.register.prod Reference).Index (child.register.prod Reference).Index ℂ)
    (keep : Store child → Store child → Prop)
    (localLaw : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State child Reference (ClassicalOracleModel.empty.HiddenState × History))
      (stored : Store child) (predicate : History → Prop),
      ((code.execute environment Reference state).filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
        ∑ outcome : Outcome, kernel Reference outcome stored *
          (state.filterClassical (fun record =>
            keep stored record.1 ∧ predicate record.2.2)).quantumMarginal.matrix *
          (kernel Reference outcome stored).conjTranspose)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State caller Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store caller) (predicate : History → Prop) :
    let coordinates := placement.referenceBasis Reference
    let finalChild := (placement.store stored).1
    let finalFrame := (placement.store stored).2
    let lifted := fun outcome : Outcome =>
      (kernel (placement.frame.register.prod Reference) outcome finalChild).submatrix
        coordinates coordinates
    (((Circuit.embed (allowAllocation := false) placement code).execute environment Reference
      state).filterClassical (fun record =>
        record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ outcome : Outcome, lifted outcome *
        (state.filterClassical (fun record =>
          keep finalChild (placement.store record.1).1 ∧
            (placement.store record.1).2 = finalFrame ∧
              predicate record.2.2)).quantumMarginal.matrix *
        (lifted outcome).conjTranspose := by
  let coordinates := placement.referenceBasis Reference
  let finalChild := (placement.store stored).1
  let finalFrame := (placement.store stored).2
  let localInput : State child (placement.frame.register.prod Reference)
      (ClassicalOracleModel.empty.HiddenState × (History × Store placement.frame)) :=
    (placement.split state).mapClassical (fun record =>
      (record.1, (record.2.2.1, (record.2.2.2, record.2.1))))
  let localOutput : State child (placement.frame.register.prod Reference)
      (ClassicalOracleModel.empty.HiddenState × ((History × Store placement.frame) × code.Path)) :=
    code.execute environment (placement.frame.register.prod Reference) localInput
  let restore := fun record : Store child ×
      (ClassicalOracleModel.empty.HiddenState ×
        ((History × Store placement.frame) × code.Path)) =>
    (record.1, (record.2.2.1.2, (record.2.1, (record.2.2.1.1, record.2.2.2))))
  have outputFiber := embed_output_store_history_matrix placement
    (Reference := Reference) (History := History) (Path := code.Path) localOutput stored predicate
  have inputFiber := embed_input_store_history_matrix placement keep
    (Reference := Reference) (History := History) state stored predicate
  have localMatrix := child_store_history_with_frame (environment := environment) code kernel keep
    localLaw
    (FrameStore := Store placement.frame) (History := History)
    (Reference := placement.frame.register.prod Reference)
    localInput finalChild finalFrame predicate
  have actualMatrix := cells_embed_filter_store_history_matrix (environment := environment)
    placement code state stored predicate
  refine actualMatrix.trans (outputFiber.trans ?_)
  exact cells_pullback_sum_sandwich coordinates
    (fun outcome : Outcome =>
      kernel (placement.frame.register.prod Reference) outcome finalChild)
    (state.filterClassical (fun record =>
      keep finalChild (placement.store record.1).1 ∧
        (placement.store record.1).2 = finalFrame ∧
          predicate record.2.2)).quantumMarginal.matrix
    (localInput.filterClassical (fun record => keep finalChild record.1 ∧
      record.2.2.2 = finalFrame ∧ predicate record.2.2.1)).quantumMarginal.matrix
    (localOutput.filterClassical (fun record => record.1 = finalChild ∧
      record.2.2.1.2 = finalFrame ∧ predicate record.2.2.1.1)).quantumMarginal.matrix
    inputFiber localMatrix

end

private lemma cells_filter_sandwich_congr {C : Type} [Fintype C]
    {R : Register} (state : ExecutionState C R) (operator : HilbertOperator R)
    {first second : C → Prop} (same : first = second)
    {firstDecision : DecidablePred first} {secondDecision : DecidablePred second} :
    operator * (@ExecutionState.filterClassical C _ R
      state first firstDecision).quantumMarginal.matrix * operator.conjTranspose =
      operator * (@ExecutionState.filterClassical C _ R
        state second secondDecision).quantumMarginal.matrix * operator.conjTranspose := by
  exact congrArg (fun matrix : HilbertOperator R =>
    operator * matrix * operator.conjTranspose)
    (cells_filter_matrix_predicate_congr state same)

private lemma pointBody_embedding_history_matrix {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (MeasuredPointAddition.context p.size)) (predicate : History → Prop) :
    let originalKernel := fun (Reference : Register)
        (divisionStore stored : Store (MeasuredPointAddition.context p.size)) =>
      (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
        divisionStore stored :
        Matrix ((MeasuredPointAddition.context p.size).register.prod Reference).Index
          ((MeasuredPointAddition.context p.size).register.prod Reference).Index ℂ)
    (((pointBody E Q).execute environment Reference state).filterClassical (fun record =>
      record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ outcome : Store (MeasuredPointAddition.context p.size),
        originalKernel Reference outcome stored *
          (state.filterClassical (fun record =>
            True ∧ predicate record.2.2)).quantumMarginal.matrix *
          (originalKernel Reference outcome stored).conjTranspose := by
  let originalKernel := fun (Reference : Register)
      (divisionStore stored : Store (MeasuredPointAddition.context p.size)) =>
    (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference divisionStore
      stored :
      Matrix ((MeasuredPointAddition.context p.size).register.prod Reference).Index
        ((MeasuredPointAddition.context p.size).register.prod Reference).Index ℂ)
  refine (pointBody_store_history_matrix E Q state stored predicate).trans ?_
  apply Finset.sum_congr rfl
  intro outcome _
  exact cells_filter_sandwich_congr
    (C := Store (MeasuredPointAddition.context p.size) ×
      (ClassicalOracleModel.empty.HiddenState × History))
    (R := (MeasuredPointAddition.context p.size).register.prod Reference) state
    (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference outcome stored)
    (first := fun record => predicate record.2.2)
    (second := fun record => True ∧ predicate record.2.2) (by
      funext record
      exact (true_and _).symm)

private lemma indexedPointCall_embedded_history_matrix {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E)
    {count : Nat} (active : Fin count) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (readyContext p.size count)) (predicate : History → Prop) :
    let inner := indexedPointPlacement p.size active
    let originalKernel := fun (Reference : Register)
        (divisionStore stored : Store (MeasuredPointAddition.context p.size)) =>
      (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
        divisionStore stored :
        Matrix ((MeasuredPointAddition.context p.size).register.prod Reference).Index
          ((MeasuredPointAddition.context p.size).register.prod Reference).Index ℂ)
    let innerKernel := fun (Reference : Register)
        (divisionStore : Store (MeasuredPointAddition.context p.size))
        (stored : Store (readyContext p.size count)) =>
      (originalKernel (inner.frame.register.prod Reference) divisionStore
        (inner.store stored).1).submatrix (inner.referenceBasis Reference)
          (inner.referenceBasis Reference)
    (((Circuit.embed (allowAllocation := false) inner (pointBody E Q)).execute environment Reference
      state).filterClassical (fun record =>
        record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ outcome : Store (MeasuredPointAddition.context p.size),
        innerKernel Reference outcome stored *
          (state.filterClassical (fun record =>
            True ∧ (inner.store record.1).2 = (inner.store stored).2 ∧
              predicate record.2.2)).quantumMarginal.matrix *
          (innerKernel Reference outcome stored).conjTranspose := by
  let inner := indexedPointPlacement p.size active
  let originalKernel := fun (Reference : Register)
      (divisionStore stored : Store (MeasuredPointAddition.context p.size)) =>
    (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference divisionStore
      stored :
      Matrix ((MeasuredPointAddition.context p.size).register.prod Reference).Index
        ((MeasuredPointAddition.context p.size).register.prod Reference).Index ℂ)
  let innerKernel := fun (Reference : Register)
      (divisionStore : Store (MeasuredPointAddition.context p.size))
      (stored : Store (readyContext p.size count)) =>
    (originalKernel (inner.frame.register.prod Reference) divisionStore
      (inner.store stored).1).submatrix (inner.referenceBasis Reference)
        (inner.referenceBasis Reference)
  have originalEmbedded := embed_store_history_matrix (environment := environment)
    (child := MeasuredPointAddition.context p.size) (caller := readyContext p.size count)
    (Outcome := Store (MeasuredPointAddition.context p.size))
    (Reference := Reference) (History := History) inner (pointBody E Q) originalKernel
    (fun _ _ => True) (by
      intro Reference History _ state stored predicate
      refine (pointBody_embedding_history_matrix E Q (Reference := Reference)
        state stored predicate).trans ?_
      apply Finset.sum_congr rfl
      intro outcome _
      exact cells_filter_sandwich_congr
        (C := Store (MeasuredPointAddition.context p.size) ×
          (ClassicalOracleModel.empty.HiddenState × History))
        (R := (MeasuredPointAddition.context p.size).register.prod Reference) state
        (originalKernel Reference outcome stored)
        (first := fun record => True ∧ predicate record.2.2)
        (second := fun record => True ∧ predicate record.2.2) rfl) state stored predicate
  refine originalEmbedded.trans ?_
  apply Finset.sum_congr rfl
  intro outcome _
  exact cells_filter_sandwich_congr
    (C := Store (readyContext p.size count) ×
      (ClassicalOracleModel.empty.HiddenState × History))
    (R := (readyContext p.size count).register.prod Reference) state
    (innerKernel Reference outcome stored)
    (first := fun record => True ∧ (inner.store record.1).2 = (inner.store stored).2 ∧
      predicate record.2.2)
    (second := fun record => True ∧ (inner.store record.1).2 = (inner.store stored).2 ∧
      predicate record.2.2) rfl

private lemma indexedPointCall_store_history_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {count : Nat} (active : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (readyContext p.size count)) (predicate : History → Prop) :
    let inner := indexedPointPlacement p.size active
    let lifted := fun outcome : Store (MeasuredPointAddition.context p.size) =>
      (Recovery.Point.Instrument.pointKraus (environment := environment) E Q
        (inner.frame.register.prod Reference) outcome
        (inner.store stored).1).submatrix (inner.referenceBasis Reference)
          (inner.referenceBasis Reference)
    (((indexedPointCall E Q active).execute environment Reference state).filterClassical
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ outcome : Store (MeasuredPointAddition.context p.size), lifted outcome *
        (state.filterClassical (fun record =>
          (inner.store record.1).2 = (inner.store stored).2 ∧
            predicate record.2.2)).quantumMarginal.matrix * (lifted outcome).conjTranspose := by
  let inner := indexedPointPlacement p.size active
  let originalKernel := fun (Reference : Register)
      (divisionStore stored : Store (MeasuredPointAddition.context p.size)) =>
    (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference divisionStore
      stored :
      Matrix ((MeasuredPointAddition.context p.size).register.prod Reference).Index
        ((MeasuredPointAddition.context p.size).register.prod Reference).Index ℂ)
  let innerKernel := fun (Reference : Register)
      (divisionStore : Store (MeasuredPointAddition.context p.size))
      (stored : Store (readyContext p.size count)) =>
    (originalKernel (inner.frame.register.prod Reference) divisionStore
      (inner.store stored).1).submatrix (inner.referenceBasis Reference)
        (inner.referenceBasis Reference)
  have callSame : indexedPointCall E Q active =
      Circuit.embed (allowAllocation := false) inner (pointBody E Q) := rfl
  have observedSame := congrArg (fun call : Circuit (.quantum AlgorithmGate.model .empty)
      (readyContext p.size count) (readyContext p.size count) false =>
    ((call.execute environment Reference state).filterClassical
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix)
    callSame
  have embedded := indexedPointCall_embedded_history_matrix (environment := environment) E Q active
    (Reference := Reference) (History := History) state stored predicate
  refine observedSame.trans (embedded.trans ?_)
  apply Finset.sum_congr rfl
  intro outcome _
  exact cells_filter_sandwich_congr
    (C := Store (readyContext p.size count) ×
      (ClassicalOracleModel.empty.HiddenState × History))
    (R := (readyContext p.size count).register.prod Reference) state
    (innerKernel Reference outcome stored)
    (first := fun record => True ∧ (inner.store record.1).2 = (inner.store stored).2 ∧
      predicate record.2.2)
    (second := fun record => (inner.store record.1).2 = (inner.store stored).2 ∧
      predicate record.2.2) (by
        funext record
        exact true_and _)

private lemma embed_store_matrix
    {child caller : RuntimeCtx .quantum} (placement : ContextEmbedding child caller)
    (code : Circuit (.quantum AlgorithmGate.model .empty) child child false)
    {Outcome : Type} [Fintype Outcome]
    (kernel : (Reference : Register) → Outcome → Store child →
      Matrix (child.register.prod Reference).Index (child.register.prod Reference).Index ℂ)
    (keep : Store child → Store child → Prop)
    (localLaw : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State child Reference (ClassicalOracleModel.empty.HiddenState × History))
      (stored : Store child) (predicate : History → Prop),
      ((code.execute environment Reference state).filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
        ∑ outcome : Outcome, kernel Reference outcome stored *
          (state.filterClassical (fun record =>
            keep stored record.1 ∧ predicate record.2.2)).quantumMarginal.matrix *
          (kernel Reference outcome stored).conjTranspose)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State caller Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store caller) :
    let coordinates := placement.referenceBasis Reference
    let finalChild := (placement.store stored).1
    let finalFrame := (placement.store stored).2
    let lifted := fun outcome : Outcome =>
      (kernel (placement.frame.register.prod Reference) outcome finalChild).submatrix
        coordinates coordinates
    (((Circuit.embed (allowAllocation := false) placement code).execute environment Reference
      state).filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix =
      ∑ outcome : Outcome, lifted outcome *
        (state.filterClassical (fun record =>
          keep finalChild (placement.store record.1).1 ∧
            (placement.store record.1).2 = finalFrame)).quantumMarginal.matrix *
          (lifted outcome).conjTranspose := by
  let coordinates := placement.referenceBasis Reference
  let finalChild := (placement.store stored).1
  let finalFrame := (placement.store stored).2
  let lifted := fun outcome : Outcome =>
    (kernel (placement.frame.register.prod Reference) outcome finalChild).submatrix
      coordinates coordinates
  let output := (Circuit.embed (allowAllocation := false) placement code).execute environment
    Reference state
  have actual := embed_store_history_matrix (environment := environment) placement code kernel
    keep localLaw
    (Reference := Reference) (History := History) state stored (fun _ => True)
  refine (cells_filter_matrix_predicate_congr output
    (first := fun record => record.1 = stored)
    (second := fun record => record.1 = stored ∧ True)
    (by funext record; exact (and_true _).symm)).trans (actual.trans ?_)
  apply Finset.sum_congr rfl
  intro outcome _
  exact cells_filter_sandwich_congr
    (C := Store caller × (ClassicalOracleModel.empty.HiddenState × History))
    (R := caller.register.prod Reference) state (lifted outcome)
    (first := fun record => keep finalChild (placement.store record.1).1 ∧
      (placement.store record.1).2 = finalFrame ∧ True)
    (second := fun record => keep finalChild (placement.store record.1).1 ∧
      (placement.store record.1).2 = finalFrame) (by
        funext record
        exact and_congr_right_eq (fun _ => and_true _))

lemma indexedPointCallWithCells_store_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {count : Nat} (active : Fin count) (cells : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (MeasurementCells.context (readyContext p.size count) 2 cells) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (MeasurementCells.context (readyContext p.size count) 2 cells)) :
    let inner := indexedPointPlacement p.size active
    let outer := cellsPlacement (readyContext p.size count) 2 cells
    let finalReady := (outer.store stored).1
    let finalCells := (outer.store stored).2
    let finalPoint := (inner.store finalReady).1
    let finalAmbient := (inner.store finalReady).2
    let outerCoordinates := outer.referenceBasis Reference
    let innerCoordinates := inner.referenceBasis (outer.frame.register.prod Reference)
    let lifted := fun divisionStore : Store (MeasuredPointAddition.context p.size) =>
      ((Recovery.Point.Instrument.pointKraus (environment := environment) E Q
        (inner.frame.register.prod (outer.frame.register.prod Reference))
        divisionStore finalPoint).submatrix innerCoordinates innerCoordinates).submatrix
          outerCoordinates outerCoordinates
    (((indexedPointCallWithCells E Q active cells).execute environment Reference
      state).filterClassical
      (fun record => record.1 = stored)).quantumMarginal.matrix =
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size), lifted divisionStore *
        (state.filterClassical (fun record =>
          (inner.store (outer.store record.1).1).2 = finalAmbient ∧
            (outer.store record.1).2 = finalCells)).quantumMarginal.matrix *
        (lifted divisionStore).conjTranspose := by
  let inner := indexedPointPlacement p.size active
  let outer := cellsPlacement (readyContext p.size count) 2 cells
  let originalKernel := fun (Reference : Register)
      (divisionStore stored : Store (MeasuredPointAddition.context p.size)) =>
    (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference divisionStore
      stored :
      Matrix ((MeasuredPointAddition.context p.size).register.prod Reference).Index
        ((MeasuredPointAddition.context p.size).register.prod Reference).Index ℂ)
  let innerKernel := fun (Reference : Register)
      (divisionStore : Store (MeasuredPointAddition.context p.size))
      (stored : Store (readyContext p.size count)) =>
    (originalKernel (inner.frame.register.prod Reference) divisionStore
      (inner.store stored).1).submatrix (inner.referenceBasis Reference)
        (inner.referenceBasis Reference)
  let innerKeep := fun stored original : Store (readyContext p.size count) =>
    (inner.store original).2 = (inner.store stored).2
  have innerLaw : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State (readyContext p.size count) Reference
        (ClassicalOracleModel.empty.HiddenState × History))
      (stored : Store (readyContext p.size count)) (predicate : History → Prop),
      (((indexedPointCall E Q active).execute environment Reference state).filterClassical
        (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
        ∑ outcome : Store (MeasuredPointAddition.context p.size),
          innerKernel Reference outcome stored *
            (state.filterClassical (fun record =>
              innerKeep stored record.1 ∧ predicate record.2.2)).quantumMarginal.matrix *
            (innerKernel Reference outcome stored).conjTranspose := by
    intro Reference History _ state stored predicate
    exact indexedPointCall_store_history_matrix E Q active state stored predicate
  have callSame : indexedPointCallWithCells E Q active cells =
      Circuit.embed (allowAllocation := false) outer (indexedPointCall E Q active) := rfl
  have observedSame := congrArg (fun call : Circuit (.quantum AlgorithmGate.model .empty)
      (MeasurementCells.context (readyContext p.size count) 2 cells)
      (MeasurementCells.context (readyContext p.size count) 2 cells) false =>
    ((call.execute environment Reference state).filterClassical
      (fun record => record.1 = stored)).quantumMarginal.matrix) callSame
  refine observedSame.trans ?_
  exact embed_store_matrix
    (child := readyContext p.size count)
    (caller := MeasurementCells.context (readyContext p.size count) 2 cells)
    (Outcome := Store (MeasuredPointAddition.context p.size))
    (Reference := Reference) (History := History) outer (indexedPointCall E Q active)
    innerKernel innerKeep innerLaw state stored

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

attribute [local irreducible] Recovery.Point.numeratorReset Recovery.Point.controlledBody
  Recovery.Point.pointBody

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement Recovery.Point

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private instance dimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

def phaseProgram (width m : Nat) (previous current : Fin (2 * m))
    (value : CShape.Value (.finite 2)) :
    UnitaryCircuit AlgorithmGate.model .empty (Context width m).quantumLayout :=
  match value with
  | .finite bit => if bit.val = 1 then
      Gate.singleQubitAt (Context width m).quantumLayout .empty
        (phaseGateOp (-(QuantumFourierTransform.Source.phaseAngle
          (current.val - previous.val - 1))))
        (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0)
    else UnitaryCircuit.identity AlgorithmGate.model .empty (Context width m).quantumLayout

def feedbackOne (width m : Nat) (previous current : Fin (2 * m)) :
    Circuit (.quantum AlgorithmGate.model .empty) (Context width m) (Context width m) false :=
  if Recovery.Layout.feeds m previous current then
    .branch (.storage (Recovery.Layout.resultCell width m previous).toCStorageRef)
      (fun value => .unitary (phaseProgram width m previous current value))
  else .id _

def feedback (width m : Nat) (current : Fin (2 * m)) : List (Fin (2 * m)) →
    Circuit (.quantum AlgorithmGate.model .empty) (Context width m) (Context width m) false
  | [] => .id _
  | previous :: tail => (feedbackOne width m previous current).seq
      (feedback width m current tail)

def correction (width m : Nat)
    (value : CShape.Value (.finite
      ((Context width m).quantumLayout.wire (Recovery.Layout.position width m 0)).dimension)) :
    UnitaryCircuit AlgorithmGate.model .empty (Context width m).quantumLayout :=
  QuditShift.qubitShiftCircuit (Context width m).quantumLayout (Recovery.Layout.position width m 0)
    (Recovery.Layout.position_qubit width m 0) .empty (-value.toFin)

def readout (width m : Nat) (index : Fin (2 * m)) :
    Circuit (.quantum AlgorithmGate.model .empty) (Context width m) (Context width m) false :=
  ((.unitary (Gate.singleQubitAt (Context width m).quantumLayout .empty Gate.HOp
    (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0))) :
      Circuit (.quantum AlgorithmGate.model .empty)
        (Context width m) (Context width m) false).seq
      (((.measureZ (Recovery.Layout.position width m 0) (output width m index)) :
        Circuit (.quantum AlgorithmGate.model .empty)
          (Context width m) (Context width m) false).seq
        (.branch (.storage (output width m index).toCStorageRef)
          (fun value => .unitary (correction width m value))))

def stage {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m)) :
    Circuit (.quantum AlgorithmGate.model .empty) (Context p.size m) (Context p.size m) false :=
  ((.unitary (Recovery.Layout.preparation p.size m r (Recovery.Layout.remaining m index))) :
      Circuit (.quantum AlgorithmGate.model .empty)
        (Context p.size m) (Context p.size m) false).seq
    ((Recovery.Point.streamingPointCall E points index).seq
      ((feedback p.size m index (Recovery.Layout.order m)).seq (readout p.size m index)))

def stages {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) : List (Fin (2 * m)) →
    Circuit (.quantum AlgorithmGate.model .empty) (Context p.size m) (Context p.size m) false
  | [] => .id _
  | index :: tail => (stage E r points index).seq (stages E r points tail)

def feedbackOneMatrix (width m : Nat) (Reference : Register)
    (previous current : Fin (2 * m)) (stored : Store (Context width m)) :
    Matrix ((Context width m).register.prod Reference).Index
      ((Context width m).register.prod Reference).Index ℂ :=
  if Recovery.Layout.feeds m previous current then
    UnitaryOperator.prodTensor
      ((phaseProgram width m previous current
        (stored.read (.storage (Recovery.Layout.resultCell width m
          previous).toCStorageRef))).matrix environment.quantum)
      (1 : UnitaryOperator Reference)
  else 1

def feedbackMatrix
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}
    (width m : Nat) (Reference : Register) (current : Fin (2 * m))
    (stored : Store (Context width m)) : List (Fin (2 * m)) →
    Matrix ((Context width m).register.prod Reference).Index
      ((Context width m).register.prod Reference).Index ℂ
  | [] => 1
  | previous :: tail => feedbackMatrix (environment := environment) width m Reference current
    stored tail *
      feedbackOneMatrix (environment := environment) width m Reference previous current stored

def readoutMatrix (width m : Nat) (Reference : Register)
    (outcome : Fin ((Context width m).quantumLayout.wire
      (Recovery.Layout.position width m 0)).dimension) :
    Matrix ((Context width m).register.prod Reference).Index
      ((Context width m).register.prod Reference).Index ℂ :=
  let x : Matrix ((Context width m).register.prod Reference).Index
      ((Context width m).register.prod Reference).Index ℂ :=
    UnitaryOperator.prodTensor ((correction width m (.finite outcome)).matrix environment.quantum)
      (1 : UnitaryOperator Reference)
  let h : Matrix ((Context width m).register.prod Reference).Index
      ((Context width m).register.prod Reference).Index ℂ :=
    UnitaryOperator.prodTensor
      ((Gate.singleQubitAt (Context width m).quantumLayout .empty Gate.HOp
        (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0)).matrix
          environment.quantum)
      (1 : UnitaryOperator Reference)
  x * ZMeasurement.projector (R := (Context width m).register.prod Reference)
    (fun basis => basis.1 (Recovery.Layout.position width m 0)) outcome * h

def pointMatrix {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (m : Nat) (Reference : Register)
    (divisionStore : Store (MeasuredPointAddition.context p.size))
    (stored : Store (Context p.size m)) :
    Matrix ((Context p.size m).register.prod Reference).Index
      ((Context p.size m).register.prod Reference).Index ℂ :=
  let inner := indexedPointPlacement p.size (0 : Fin 2)
  let outer := cellsPlacement (readyContext p.size 2) 2 (2 * m)
  let innerCoordinates := inner.referenceBasis (outer.frame.register.prod Reference)
  let outerCoordinates := outer.referenceBasis Reference
  ((Recovery.Point.Instrument.pointKraus (environment := environment) E Q
    (inner.frame.register.prod (outer.frame.register.prod Reference)) divisionStore
    (inner.store (outer.store stored).1).1).submatrix
      innerCoordinates innerCoordinates).submatrix outerCoordinates outerCoordinates

def preparationMatrix (width m r : Nat) (index : Fin (2 * m)) (Reference : Register) :
    Matrix ((Context width m).register.prod Reference).Index
      ((Context width m).register.prod Reference).Index ℂ :=
  UnitaryOperator.prodTensor
    ((Recovery.Layout.preparation width m r (Recovery.Layout.remaining m index)).matrix
      environment.quantum)
    (1 : UnitaryOperator Reference)

def stageMatrix {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    (Reference : Register) (stored : Store (Context p.size m))
    (outcome : Fin ((Context p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (divisionStore : Store (MeasuredPointAddition.context p.size)) :
    Matrix ((Context p.size m).register.prod Reference).Index
      ((Context p.size m).register.prod Reference).Index ℂ :=
  readoutMatrix (environment := environment) p.size m Reference outcome *
    feedbackMatrix (environment := environment) p.size m Reference index stored
      (Recovery.Layout.order m) *
    pointMatrix (environment := environment) E (points index) m Reference divisionStore stored *
    preparationMatrix (environment := environment) p.size m r index Reference

private lemma id_store_matrix {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store ctx) :
    (((Circuit.id (allowAllocation := false)
      (model := .quantum AlgorithmGate.model .empty) ctx).execute environment Reference
        state).filterClassical
        (fun record => record.1 = stored)).quantumMarginal.matrix =
      (state.filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix := by
  let output : State ctx Reference
      (ClassicalOracleModel.empty.HiddenState × (History × Unit)) :=
    (Circuit.id (allowAllocation := false)
      (model := .quantum AlgorithmGate.model .empty) ctx).execute environment Reference state
  have actual : output =
      state.mapClassical (fun record => (record.1, (record.2.1, (record.2.2, ())))) :=
    (Circuit.execute_id (environment := environment) (allowAllocation := false)
      (model := .quantum AlgorithmGate.model .empty) state).trans
      (ExecutionState.executionState_mapClassical_congr state rfl)
  refine (congrArg (fun result : State ctx Reference
      (ClassicalOracleModel.empty.HiddenState × (History × Unit)) =>
    (result.filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix)
    actual).trans ?_
  exact cells_map_filter_matrix_decisions state _ _

private lemma feedbackOne_store_matrix (width m : Nat) (previous current : Fin (2 * m))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context width m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (Context width m)) :
    (((feedbackOne width m previous current).execute environment Reference state).filterClassical
      (fun record => record.1 = stored)).quantumMarginal.matrix =
      feedbackOneMatrix (environment := environment) width m Reference previous current stored *
        (state.filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix *
        (feedbackOneMatrix (environment := environment) width m Reference previous current
          stored).conjTranspose := by
  by_cases selected : Recovery.Layout.feeds m previous current
  · let selectedCode : Circuit (.quantum AlgorithmGate.model .empty)
        (Context width m) (Context width m) false :=
      .branch (.storage (Recovery.Layout.resultCell width m previous).toCStorageRef)
        (fun value => .unitary (phaseProgram width m previous current value))
    have codeSame : feedbackOne width m previous current = selectedCode :=
      if_pos selected
    have actualMatrix := congrArg (fun code : Circuit (.quantum AlgorithmGate.model .empty)
        (Context width m) (Context width m) false =>
      ((code.execute environment Reference state).filterClassical
        (fun record => record.1 = stored)).quantumMarginal.matrix) codeSame
    refine actualMatrix.trans ?_
    have selectedMatrix := (Circuit.selectedUnitary_store_matrix (allowAllocation := false)
        (operations := .empty) (classicalOracles := .empty)
        (.storage (Recovery.Layout.resultCell width m previous).toCStorageRef)
        (phaseProgram width m previous current) environment state stored).trans
          (DensityOperator.applyUnitary_matrix _ _)
    refine selectedMatrix.trans ?_
    simp only [feedbackOneMatrix, if_pos selected]
  · let identityCode : Circuit (.quantum AlgorithmGate.model .empty)
        (Context width m) (Context width m) false := .id _
    have codeSame : feedbackOne width m previous current = identityCode :=
      if_neg selected
    have actualMatrix := congrArg (fun code : Circuit (.quantum AlgorithmGate.model .empty)
        (Context width m) (Context width m) false =>
      ((code.execute environment Reference state).filterClassical
        (fun record => record.1 = stored)).quantumMarginal.matrix) codeSame
    refine actualMatrix.trans ((id_store_matrix state stored).trans ?_)
    simp only [feedbackOneMatrix, if_neg selected, Matrix.one_mul,
      Matrix.mul_one, Matrix.conjTranspose_one]

lemma feedback_store_matrix (width m : Nat) (current : Fin (2 * m))
    (indices : List (Fin (2 * m))) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (Context width m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (Context width m)) :
    (((feedback width m current indices).execute environment Reference state).filterClassical
      (fun record => record.1 = stored)).quantumMarginal.matrix =
      feedbackMatrix (environment := environment) width m Reference current stored indices *
        (state.filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix *
        (feedbackMatrix (environment := environment) width m Reference current stored
          indices).conjTranspose := by
  induction indices generalizing History with
  | nil =>
      have codeSame : feedback width m current [] =
          Circuit.id (allowAllocation := false)
            (model := .quantum AlgorithmGate.model .empty) (Context width m) := rfl
      have actualMatrix := congrArg (fun code : Circuit (.quantum AlgorithmGate.model .empty)
          (Context width m) (Context width m) false =>
        ((code.execute environment Reference state).filterClassical
          (fun record => record.1 = stored)).quantumMarginal.matrix) codeSame
      refine actualMatrix.trans ((id_store_matrix state stored).trans ?_)
      simp only [feedbackMatrix, Matrix.one_mul, Matrix.mul_one, Matrix.conjTranspose_one]
  | cons previous tail ih =>
      refine (congrArg DensityOperator.matrix
        (Circuit.seq_store_marginal (environment := environment) (feedbackOne width m previous
          current)
          (feedback width m current tail) state stored)).trans ?_
      let output : State (Context width m) Reference
          (ClassicalOracleModel.empty.HiddenState ×
            (History × (feedbackOne width m previous current).Path)) :=
        (feedbackOne width m previous current).execute environment Reference state
      have tailMatrix := ih output
      have oneMatrix := feedbackOne_store_matrix (environment := environment) width m previous
        current state stored
      have transported := congrArg (fun matrix : HilbertOperator
          ((Context width m).register.prod Reference) =>
        feedbackMatrix (environment := environment) width m Reference current stored tail * matrix *
          (feedbackMatrix (environment := environment) width m Reference current stored
            tail).conjTranspose) oneMatrix
      refine tailMatrix.trans (transported.trans ?_)
      simp only [feedbackMatrix, Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma readout_store_matrix (width m : Nat) (index : Fin (2 * m))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context width m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (Context width m)) :
    (((readout width m index).execute environment Reference state).filterClassical
      (fun record => record.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store (Context width m),
        ∑ outcome : Fin ((Context width m).quantumLayout.wire
          (Recovery.Layout.position width m 0)).dimension,
          if original.write (output width m index) (.finite outcome) = stored then
            readoutMatrix (environment := environment) width m Reference outcome *
              (state.filterClassical (fun record => record.1 = original)).quantumMarginal.matrix *
              (readoutMatrix (environment := environment) width m Reference outcome).conjTranspose
          else 0 := by
  have actual :
      (((readout width m index).execute environment Reference state).filterClassical
        (fun record => record.1 = stored)).quantumMarginal.matrix =
        ∑ original : Store (Context width m) × (ClassicalOracleModel.empty.HiddenState × History),
          ∑ outcome : Fin ((Context width m).quantumLayout.wire
            (Recovery.Layout.position width m 0)).dimension,
            if original.1.write (output width m index) (.finite outcome) = stored then
              readoutMatrix (environment := environment) width m Reference outcome * (state.block
                original).matrix *
                (readoutMatrix (environment := environment) width m Reference outcome).conjTranspose
            else 0 := by
    exact Circuit.unitary_measureZ_selected_store_matrix
      (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := .empty) (services := .empty)
      (Gate.singleQubitAt (Context width m).quantumLayout .empty Gate.HOp
        (Recovery.Layout.position width m 0) (Recovery.Layout.position_qubit width m 0))
      (Recovery.Layout.position width m 0) (output width m index) (correction width m)
      environment state stored
  refine actual.trans ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro original _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : original.write (output width m index) (.finite outcome) = stored
  · simp only [if_pos written]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum]
    have historySum :
        (state.filterClassical (fun record => record.1 = original)).quantumMarginal.matrix =
          ∑ history : ClassicalOracleModel.empty.HiddenState × History,
            (state.block (original, history)).matrix :=
      QuantumFourierTransform.Semiclassical.stored_matrix_sum_history state original
    exact congrArg (fun matrix : HilbertOperator ((Context width m).register.prod Reference) =>
      readoutMatrix (environment := environment) width m Reference outcome * matrix *
        (readoutMatrix (environment := environment) width m Reference outcome).conjTranspose)
          historySum.symm
  · simp only [if_neg written, Finset.sum_const_zero]

private lemma point_store_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (Context p.size m)) :
    (((Recovery.Point.streamingPointCall E points index).execute environment Reference
      state).filterClassical
      (fun record => record.1 = stored)).quantumMarginal.matrix =
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        pointMatrix (environment := environment) E (points index) m Reference divisionStore stored *
          (state.filterClassical
            (fun record => retains p.size m stored record.1)).quantumMarginal.matrix *
          (pointMatrix (environment := environment) E (points index) m Reference divisionStore
            stored).conjTranspose := by
  have callSame : Recovery.Point.streamingPointCall E points index =
      indexedPointCallWithCells E (points index) (0 : Fin 2) (2 * m) := rfl
  have observedSame := congrArg (fun call : Circuit (.quantum AlgorithmGate.model .empty)
      (Context p.size m) (Context p.size m) false =>
    ((call.execute environment Reference state).filterClassical
      (fun record => record.1 = stored)).quantumMarginal.matrix) callSame
  have actual := indexedPointCallWithCells_store_matrix (environment := environment) E (points
    index)
    (0 : Fin 2) (2 * m) state stored
  refine observedSame.trans (actual.trans ?_)
  apply Finset.sum_congr rfl
  intro divisionStore _
  let inner := indexedPointPlacement p.size (0 : Fin 2)
  let outer := cellsPlacement (readyContext p.size 2) 2 (2 * m)
  have kernelSame :
      ((Recovery.Point.Instrument.pointKraus (environment := environment) E (points index)
        (inner.frame.register.prod (outer.frame.register.prod Reference)) divisionStore
        (inner.store (outer.store stored).1).1).submatrix
          (inner.referenceBasis (outer.frame.register.prod Reference))
          (inner.referenceBasis (outer.frame.register.prod Reference))).submatrix
            (outer.referenceBasis Reference) (outer.referenceBasis Reference) =
        pointMatrix (environment := environment) E (points index) m Reference divisionStore stored
          := rfl
  refine (congrArg (fun operator : HilbertOperator ((Context p.size m).register.prod Reference) =>
    operator * (state.filterClassical (fun record =>
      (inner.store (outer.store record.1).1).2 = (inner.store (outer.store stored).1).2 ∧
        (outer.store record.1).2 = (outer.store stored).2)).quantumMarginal.matrix *
      operator.conjTranspose) kernelSame).trans ?_
  apply congrArg (fun matrix : HilbertOperator ((Context p.size m).register.prod Reference) =>
    pointMatrix (environment := environment) E (points index) m Reference divisionStore stored *
      matrix *
      (pointMatrix (environment := environment) E (points index) m Reference divisionStore
        stored).conjTranspose)
  exact cells_filter_matrix_predicate_congr state rfl

private lemma unitary_selected_matrix {ctx : RuntimeCtx .quantum}
    (program : UnitaryCircuit AlgorithmGate.model .empty ctx.quantumLayout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : Store ctx → Prop) :
    let operator := UnitaryOperator.prodTensor (program.matrix environment.quantum)
      (1 : UnitaryOperator Reference)
    (((Circuit.unitary (allowAllocation := false) (operations := .empty)
      (classicalOracles := .empty) program).execute environment Reference state).filterClassical
        (fun record => predicate record.1)).quantumMarginal.matrix =
      (operator : HilbertOperator (ctx.register.prod Reference)) *
        (state.filterClassical (fun record => predicate record.1)).quantumMarginal.matrix *
        (operator : HilbertOperator (ctx.register.prod Reference)).conjTranspose := by
  let operator := UnitaryOperator.prodTensor (program.matrix environment.quantum)
      (1 : UnitaryOperator Reference)
  have law := congrArg DensityOperator.matrix
    (Circuit.unitary_store_filter (environment := environment) (allowAllocation := false)
      (operations := .empty) (services := .empty) (ctx := ctx)
      (Reference := Reference) (History := History) program state predicate)
  refine (cells_filter_matrix_predicate_congr
    ((Circuit.unitary (allowAllocation := false) (operations := .empty)
      (classicalOracles := .empty) program).execute environment Reference state) rfl).trans
    (law.trans ?_)
  refine (DensityOperator.applyUnitary_matrix _ _).trans ?_
  exact cells_filter_sandwich_congr
    (C := Store ctx × (ClassicalOracleModel.empty.HiddenState × History))
    (R := ctx.register.prod Reference) state operator
    (first := fun record => predicate record.1)
    (second := fun record => predicate record.1) rfl

private lemma four_matrix_sandwiches {R : Register}
    (readout feedback point preparation selected initial : HilbertOperator R)
    (prepared : selected = preparation * initial * preparation.conjTranspose) :
    readout * (feedback * (point * selected * point.conjTranspose) *
      feedback.conjTranspose) * readout.conjTranspose =
        (readout * feedback * point * preparation) * initial *
          (readout * feedback * point * preparation).conjTranspose := by
  rw [prepared]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

private lemma preparation_store_matrix (width m r : Nat) (index : Fin (2 * m))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context width m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (Context width m)) :
    (((Circuit.unitary (allowAllocation := false) (operations := .empty)
      (classicalOracles := .empty)
      (Recovery.Layout.preparation width m r (Recovery.Layout.remaining m index))).execute
        environment Reference state).filterClassical
          (fun record => retains width m stored record.1)).quantumMarginal.matrix =
      preparationMatrix (environment := environment) width m r index Reference *
        (state.filterClassical (fun record =>
          retains width m stored record.1)).quantumMarginal.matrix *
        (preparationMatrix (environment := environment) width m r index
          Reference).conjTranspose := by
  exact unitary_selected_matrix (ctx := Context width m)
    (Reference := Reference) (History := History)
    (Recovery.Layout.preparation width m r (Recovery.Layout.remaining m index)) state
    (retains width m stored)

private lemma stage_preparation_sandwich {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (intermediate : Store (Context p.size m))
    (outcome : Fin ((Context p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (divisionStore : Store (MeasuredPointAddition.context p.size)) :
    let preparation : Circuit (.quantum AlgorithmGate.model .empty)
        (Context p.size m) (Context p.size m) false :=
      .unitary (Recovery.Layout.preparation p.size m r (Recovery.Layout.remaining m index))
    let selected := ((preparation.execute environment Reference state).filterClassical (fun record
      =>
      retains p.size m intermediate record.1)).quantumMarginal.matrix
    readoutMatrix (environment := environment) p.size m Reference outcome *
      (feedbackMatrix (environment := environment) p.size m Reference index intermediate
        (Recovery.Layout.order m) *
        (pointMatrix (environment := environment) E (points index) m Reference divisionStore
          intermediate * selected *
          (pointMatrix (environment := environment) E (points index) m Reference divisionStore
            intermediate).conjTranspose) *
        (feedbackMatrix (environment := environment) p.size m Reference index intermediate
          (Recovery.Layout.order m)).conjTranspose) *
      (readoutMatrix (environment := environment) p.size m Reference outcome).conjTranspose =
        stageMatrix (environment := environment) E r points index Reference intermediate outcome
          divisionStore *
          (state.filterClassical (fun record =>
            retains p.size m intermediate record.1)).quantumMarginal.matrix *
          (stageMatrix (environment := environment) E r points index Reference intermediate outcome
            divisionStore).conjTranspose := by
  simpa only [stageMatrix] using
    (four_matrix_sandwiches (R := (Context p.size m).register.prod Reference)
      (readoutMatrix (environment := environment) p.size m Reference outcome)
      (feedbackMatrix (environment := environment) p.size m Reference index intermediate
        (Recovery.Layout.order m))
      (pointMatrix (environment := environment) E (points index) m Reference divisionStore
        intermediate)
      (preparationMatrix (environment := environment) p.size m r index Reference)
      _ _ (preparation_store_matrix p.size m r index
        (Reference := Reference) (History := History) state intermediate))

lemma stage_store_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (index : Fin (2 * m))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (Context p.size m)) :
    (((stage E r points index).execute environment Reference state).filterClassical
      (fun record => record.1 = stored)).quantumMarginal.matrix =
      ∑ intermediate : Store (Context p.size m),
        ∑ outcome : Fin ((Context p.size m).quantumLayout.wire
          (Recovery.Layout.position p.size m 0)).dimension,
          ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
            if intermediate.write (output p.size m index) (.finite outcome) = stored then
              stageMatrix (environment := environment) E r points index Reference intermediate
                outcome divisionStore *
                (state.filterClassical (fun record =>
                  retains p.size m intermediate record.1)).quantumMarginal.matrix *
                (stageMatrix (environment := environment) E r points index Reference intermediate
                  outcome divisionStore).conjTranspose
            else 0 := by
  let preparation : Circuit (.quantum AlgorithmGate.model .empty)
      (Context p.size m) (Context p.size m) false :=
    .unitary (Recovery.Layout.preparation p.size m r (Recovery.Layout.remaining m index))
  let preparedState : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × (History × preparation.Path)) :=
    preparation.execute environment Reference state
  let pointed : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        ((History × preparation.Path) × (Recovery.Point.streamingPointCall E points index).Path)) :=
    (Recovery.Point.streamingPointCall E points index).execute environment Reference preparedState
  let fed : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        (((History × preparation.Path) × (Recovery.Point.streamingPointCall E points index).Path) ×
          (feedback p.size m index (Recovery.Layout.order m)).Path)) :=
    (feedback p.size m index (Recovery.Layout.order m)).execute environment Reference pointed
  have actual :
      (((stage E r points index).execute environment Reference state).filterClassical
        (fun record => record.1 = stored)).quantumMarginal.matrix =
        (((readout p.size m index).execute environment Reference fed).filterClassical
          (fun record => record.1 = stored)).quantumMarginal.matrix := by
    exact (congrArg DensityOperator.matrix
      (Circuit.seq_store_marginal (environment := environment) preparation
        ((Recovery.Point.streamingPointCall E points index).seq
          ((feedback p.size m index (Recovery.Layout.order m)).seq (readout p.size m index)))
        state stored)).trans
      ((congrArg DensityOperator.matrix
        (Circuit.seq_store_marginal (environment := environment) (Recovery.Point.streamingPointCall
          E points index)
          ((feedback p.size m index (Recovery.Layout.order m)).seq (readout p.size m index))
          preparedState stored)).trans
        (congrArg DensityOperator.matrix
          (Circuit.seq_store_marginal (environment := environment) (feedback p.size m index
            (Recovery.Layout.order m))
            (readout p.size m index) pointed stored)))
  refine actual.trans ((readout_store_matrix p.size m index fed stored).trans ?_)
  apply Finset.sum_congr rfl
  intro intermediate _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : intermediate.write (output p.size m index) (.finite outcome) = stored
  · simp only [if_pos written]
    have feedbackLaw := feedback_store_matrix (environment := environment) p.size m index
      (Recovery.Layout.order m)
      pointed intermediate
    have feedbackObserved := congrArg (fun matrix : HilbertOperator
        ((Context p.size m).register.prod Reference) =>
      readoutMatrix (environment := environment) p.size m Reference outcome * matrix *
        (readoutMatrix (environment := environment) p.size m Reference outcome).conjTranspose)
          feedbackLaw
    refine feedbackObserved.trans ?_
    have pointLaw := point_store_matrix (environment := environment) E points index preparedState
      intermediate
    have pointObserved := congrArg (fun matrix : HilbertOperator
        ((Context p.size m).register.prod Reference) =>
      readoutMatrix (environment := environment) p.size m Reference outcome *
        (feedbackMatrix (environment := environment) p.size m Reference index intermediate
          (Recovery.Layout.order m) * matrix *
          (feedbackMatrix (environment := environment) p.size m Reference index intermediate
            (Recovery.Layout.order m)).conjTranspose) *
        (readoutMatrix (environment := environment) p.size m Reference outcome).conjTranspose)
          pointLaw
    refine pointObserved.trans ?_
    rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro divisionStore _
    exact stage_preparation_sandwich E r points index
      (Reference := Reference) (History := History) state intermediate outcome divisionStore
  · simp only [if_neg written, Finset.sum_const_zero]

lemma stages_nil_execute {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (stages E r points []).execute environment Reference state =
      state.mapClassical (fun record => (record.1, (record.2.1, (record.2.2, ())))) :=
  (Circuit.execute_id (environment := environment) (allowAllocation := false)
    (model := .quantum AlgorithmGate.model .empty) state).trans
      (ExecutionState.executionState_mapClassical_congr state rfl)

lemma stages_cons_execute {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (index : Fin (2 * m)) (tail : List (Fin (2 * m)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (stages E r points (index :: tail)).execute environment Reference state =
      ((stages E r points tail).execute environment Reference
        ((stage E r points index).execute environment Reference state)).mapHistory
          (fun record => (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
  Circuit.execute_seq (environment := environment) (stage E r points index) (stages E r points
    tail) state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
