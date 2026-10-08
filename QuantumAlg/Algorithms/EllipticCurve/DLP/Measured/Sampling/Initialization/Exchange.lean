/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Initialization.State

/-!
# Complete execution exchange of original exponent preparation and initialization

The actual initialization record keeps the same classical values and the same
retained-cell path when an earlier mathematical history is regrouped. Combined
with the full block tensor identity, this exchanges the actual exponent
instruction with the actual two preparations and all original result retains.
Only the mathematical execution path is reordered.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion MeasuredUncompute ScalarMultiplication.MeasuredPlacement
open ScalarMultiplication.MeasuredPlacement.Allocation MAU.Inversion.SharedEEA
open GenericPointAddition.InPlace MeasurementCells

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem initializationBlocks_unitary (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    {C : Type} [Fintype C] {Reference : Register}
    (state : ExecutionState C
      (Register.prod (before modulus.size (2 * exponentWidth)).register Reference)) :
    (initializationBlocks modulus (2 * exponentWidth) state).applyUnitary
        (fun _ => UnitaryOperator.prodTensor
          (afterExponentProgram modulus exponentWidth program).matrix
          (1 : UnitaryOperator Reference)) =
      initializationBlocks modulus (2 * exponentWidth)
        (state.applyUnitary fun _ =>
          beforeExponentOperator modulus exponentWidth program Reference) := by
  apply ExecutionState.ext
  intro label
  exact afterExponentOperator_initializedDensity modulus exponentWidth program
    Reference (state.block label)

private theorem initializeWork_applyUnitary (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size (2 * exponentWidth)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((initializeWork modulus (2 * exponentWidth)).execute Reference state).applyUnitary
        (fun _ => UnitaryOperator.prodTensor
          (afterExponentProgram modulus exponentWidth program).matrix
          (1 : UnitaryOperator Reference)) =
      ((initializeWork modulus (2 * exponentWidth)).execute Reference
        (state.applyUnitary fun _ =>
          beforeExponentOperator modulus exponentWidth program Reference)) := by
  rw [initializeWork_execute, initializeWork_execute]
  rw [ExecutionState.applyUnitary_mapClassical]
  rw [initializationBlocks_unitary]

section ActualExchange

attribute [local irreducible] Circuit.execute State.unitary State.mapHistory
  ExecutionState.mapClassical

private theorem initializeWork_exponentCircuit_execute_normalized (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size (2 * exponentWidth)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((initializeWork modulus (2 * exponentWidth)).seq
      (Circuit.unitary (operations := .empty) (classicalOracles := .empty)
        (afterExponentProgram modulus exponentWidth program))).execute Reference state =
      (((Circuit.unitary (operations := .empty) (classicalOracles := .empty)
        (beforeExponentProgram modulus exponentWidth program)).seq
        (initializeWork modulus (2 * exponentWidth))).execute Reference state).mapHistory
          (fun record => (record.1,
            (record.2.1, (record.2.2.2, record.2.2.1)))) := by
  rw [Circuit.execute_seq, Circuit.execute_seq]
  rw [Circuit.execute_unitary, Circuit.execute_unitary]
  erw [initializeWork_applyUnitary]
  have beforeHistory :
      (state.applyUnitary fun _ =>
        beforeExponentOperator modulus exponentWidth program Reference).mapClassical
          (fun value => (value.1, (value.2.1, (value.2.2, ())))) =
        State.mapHistory
          (state.applyUnitary fun _ =>
            beforeExponentOperator modulus exponentWidth program Reference)
          (fun record => (record.1, (record.2, ()))) := by
    unfold State.mapHistory
    exact ExecutionState.executionState_mapClassical_congr _ rfl
  erw [beforeHistory]
  erw [Circuit.execute_mapHistory (initializeWork modulus (2 * exponentWidth))
    Reference (state.applyUnitary fun _ =>
      beforeExponentOperator modulus exponentWidth program Reference)
    (fun history : History => (history, ()))]
  simp only [State.mapHistory,
    ExecutionState.executionState_mapClassical_comp_instances, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- The actual original exponent instruction commutes with initialization in the complete State. -/
theorem initializeWork_exponentCircuit_execute (modulus exponentWidth : Nat)
    (program : UnitaryCircuit AlgorithmGate.model .empty
      (QuantumSignature.qubits (exponentWidth + exponentWidth)).canonicalPlacement.layout)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (before modulus.size (2 * exponentWidth)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    ((initializeWork modulus (2 * exponentWidth)).seq
      (afterExponentCircuit modulus exponentWidth program)).execute Reference state =
      (((beforeExponentCircuit modulus exponentWidth program).seq
        (initializeWork modulus (2 * exponentWidth))).execute Reference state).mapHistory
          (fun record => (record.1,
            (record.2.1, (record.2.2.2, record.2.2.1)))) := by
  unfold beforeExponentCircuit afterExponentCircuit
  convert initializeWork_exponentCircuit_execute_normalized
    modulus exponentWidth program state using 1

end ActualExchange

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
