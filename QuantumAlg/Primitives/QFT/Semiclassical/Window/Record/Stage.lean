/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Stage
import all QuantumAlg.Core.Execution.Selected.Store
import all QuantumAlg.Core.Execution.Classical.MapLaws
import all QuantumAlg.Core.Execution.Measurement.Effect

/-!
# Full records of the actual corrected Fourier head

The real H/MZ/selected phase-and-X interpreter retains its original Store,
persistent service state, history, and complete measured Path. In particular,
overwriting the measured cell sums all colliding original records. These
equations concern the existing circuit, including every off-diagonal external
reference entry, rather than a supplied instrument or a Store-only marginal.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- The same measured outcome determines the actual write and selected branch Path. -/
def stageStoreRecord (ports : Ports ctx totalBits (active + 1))
    (store : Store ctx)
    (outcome : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension) :
    Store ctx × (stage (operations := operations) (services := services) ports).Path :=
  (store.write (ports.measuredOutput 0) (.finite outcome),
    ((), (outcome, ⟨.finite outcome, ()⟩)))

/-- Original service state and incoming history are retained alongside the actual head Path. -/
def stageRecord (ports : Ports ctx totalBits (active + 1)) {History : Type}
    (entry : Store ctx × (services.HiddenState × History))
    (outcome : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension) :
    Store ctx × (services.HiddenState ×
      (History × (stage (operations := operations) (services := services) ports).Path)) :=
  let next := stageStoreRecord (operations := operations) (services := services) ports
    entry.1 outcome
  (next.1, (entry.2.1, (entry.2.2, next.2)))

/-- Exact execution with the real measurement record and same-cell selected native correction. -/
lemma window_stage_execute_record (ports : Ports ctx totalBits (active + 1))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (stage ports).execute environment Reference state =
      ((ExecutionState.measureZ
        (state.applyUnitary fun _ => UnitaryOperator.prodTensor
          ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp (ports.wires 0)
            (ports.qubits 0)).matrix environment.quantum) (1 : UnitaryOperator Reference))
        (fun basis : (Register.prod ctx.register Reference).Index =>
          basis.1 (ports.wires 0))).applyUnitary
        fun entry => UnitaryOperator.prodTensor
          ((afterHead ports (.finite entry.2)).matrix environment.quantum)
          (1 : UnitaryOperator Reference)).mapClassical
            (fun entry => stageRecord (operations := operations) ports entry.1 entry.2) := by
  unfold stage
  rw [Circuit.execute_seq, Circuit.execute_unitary,
    Circuit.execute_seq, Circuit.execute_measureZ, Circuit.selectedUnitary_execute]
  simp only [State.mapHistory, ExecutionState.mapClassical_measureZ,
    ExecutionState.applyUnitary_mapClassical, Store.read_write_same,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  have readBack :
      (fun entry : (Store ctx × (services.HiddenState × History)) ×
          Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension =>
        (show Store ctx × (services.HiddenState ×
          (History × (stage (operations := operations) (services := services) ports).Path)) from
          (entry.1.1.write (ports.measuredOutput 0) (.finite entry.2),
            (entry.1.2.1, (entry.1.2.2, ((), (entry.2,
              ⟨(entry.1.1.write (ports.measuredOutput 0) (.finite entry.2)).read
                (.storage (ports.measuredOutput 0).toCStorageRef), ()⟩))))))) =
      (fun entry => stageRecord (operations := operations) ports entry.1 entry.2) := by
    funext entry
    exact congrArg
      (fun value : (CShape.finite (ctx.quantumLayout.wire (ports.wires 0)).dimension).Value =>
        (show Store ctx × (services.HiddenState ×
          (History × (stage (operations := operations) (services := services) ports).Path)) from
          (entry.1.1.write (ports.measuredOutput 0) (.finite entry.2),
            (entry.1.2.1, (entry.1.2.2, ((), (entry.2, ⟨value, ()⟩)))))))
      (Store.read_write_same entry.1.1 (ports.measuredOutput 0) (.finite entry.2))
  have updated := congrArg (fun update =>
    ((ExecutionState.measureZ
      (state.applyUnitary fun _ => UnitaryOperator.prodTensor
        ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp (ports.wires 0)
          (ports.qubits 0)).matrix environment.quantum) (1 : UnitaryOperator Reference))
      (fun basis : (Register.prod ctx.register Reference).Index =>
        basis.1 (ports.wires 0))).applyUnitary
      fun entry => UnitaryOperator.prodTensor
        ((afterHead ports (.finite entry.2)).matrix environment.quantum)
        (1 : UnitaryOperator Reference)).mapClassical update) readBack
  refine Eq.trans ?_ updated
  congr 1
  exact Subsingleton.elim _ _

/-- Every full output record has precisely its original corrected Fourier Kraus branches. -/
lemma window_stage_record_block_matrix (ports : Ports ctx totalBits (active + 1))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState ×
      (History × (stage (operations := operations) (services := services) ports).Path)))
    (left right : (Register.prod ctx.register Reference).Index) :
    (((stage ports).execute environment Reference state).block result).matrix left right =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ outcome : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension,
          if stageRecord (operations := operations) ports original outcome = result then
            (nativeStageKraus ports environment.quantum Reference outcome *
              (state.block original).matrix *
                (nativeStageKraus ports environment.quantum Reference outcome).conjTranspose)
              left right
          else 0 := by
  rw [window_stage_execute_record, ExecutionState.mapClassical_block_matrix]
  simp only [Matrix.sum_apply, ExecutionState.applyUnitary_block]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  split_ifs
  · rw [ExecutionState.measureZ_block]
    simp only [ExecutionState.applyUnitary_block, DensityOperator.applyUnitary_matrix,
      ZMeasurement.branch, nativeStageKraus,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · rfl

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
