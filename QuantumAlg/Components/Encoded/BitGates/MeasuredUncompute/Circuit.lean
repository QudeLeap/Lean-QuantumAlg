/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.QuditShift.Qubit
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Semantics
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.Selected.Store

import all QuantumAlg.Core.Execution.Classical.MapLaws

/-!
# Physical X-basis measurement and stored-result reset

One native Hadamard precedes the actual Z measurement, Store write, Store
read, and selected identity/X correction. The result remains in the supplied
classical cell and the physical wire remains present in its zero state.
No input cell value, normalization or separability assumption is made.
The retained measurement character is corrected separately by the consumer
[G25, main.tex:199-295].
-/

namespace QuantumAlg.EncodedBit.MeasuredUncompute

noncomputable section

private instance dimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

open Execution

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {oracles : OracleModel} {ctx : RuntimeCtx .quantum}

/-- One native Hadamard at the existing selected physical wire. -/
def hadamard (wire : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire wire).dimension = 2) :
    UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout :=
  Gate.singleQubitAt ctx.quantumLayout oracles Gate.HOp wire qubit

/-- Execute H, MZ, a write/read of its actual outcome, and its physical identity/X reset. -/
def circuit (wire : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty)
    (allowAllocation : Bool := true) :
    Circuit (.quantum AlgorithmGate.model oracles operations services) ctx ctx allowAllocation :=
  (Circuit.unitary (hadamard wire qubit)).seq
    (QuditShift.resetCircuit wire output
      (QuditShift.qubitRealizations ctx.quantumLayout wire qubit oracles) operations services
        allowAllocation)

/-- The actual finite record keeps the incoming history and overwrites exactly the measured cell. -/
def record (wire : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (operations : ClassicalOpModel := .empty) (services : ClassicalOracleModel := .empty)
    {allowAllocation : Bool} {History : Type}
    (entry : Store ctx × (services.HiddenState × History))
    (outcome : Fin (ctx.quantumLayout.wire wire).dimension) :
    Store ctx × (services.HiddenState ×
      (History × (circuit (oracles := oracles) wire qubit output operations services
        allowAllocation).Path)) :=
  (entry.1.write output (.finite outcome),
    (entry.2.1, (entry.2.2, ((), (outcome, ⟨.finite outcome, ()⟩)))))

/-- Full actual execution, retaining each original Store, history, measured outcome and reference.
The final finite map includes all collisions caused by overwriting the measured cell. -/
lemma execute {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    {allowAllocation : Bool}
    (wire : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (output : CWriteRef ctx (.finite (ctx.quantumLayout.wire wire).dimension))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles operations
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (circuit wire qubit output operations services allowAllocation).execute
        environment Reference state =
      ((ExecutionState.measureZ
        (state.applyUnitary fun _ => UnitaryOperator.prodTensor
          ((hadamard wire qubit).matrix environment.quantum)
          (1 : UnitaryOperator Reference))
        (fun basis : (Register.prod ctx.register Reference).Index => basis.1 wire)).applyUnitary
          fun entry => UnitaryOperator.prodTensor
            (QuditShift.operator ctx.quantumLayout wire (-entry.2))
            (1 : UnitaryOperator Reference)).mapClassical
              (fun entry => record (oracles := oracles) wire qubit output operations services
                entry.1 entry.2) := by
  unfold circuit QuditShift.resetCircuit
  rw [Circuit.execute_seq, Circuit.execute_unitary,
    Circuit.execute_seq, Circuit.execute_measureZ, Circuit.selectedUnitary_execute]
  simp only [State.mapHistory, ExecutionState.mapClassical_measureZ,
    ExecutionState.applyUnitary_mapClassical, Store.read_write_same,
    CShape.Value.toFin_finite, UnitaryCircuit.ExactRealization.matrix_eq,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  have readBack :
      (fun entry : (Store ctx × (services.HiddenState × History)) ×
          Fin (ctx.quantumLayout.wire wire).dimension =>
        (show Store ctx × (services.HiddenState ×
        (History × (circuit (oracles := oracles) wire qubit output operations services
          allowAllocation).Path)) from
          (entry.1.1.write output (.finite entry.2),
          (entry.1.2.1, (entry.1.2.2, ((), (entry.2,
            ⟨(entry.1.1.write output (.finite entry.2)).read
              (.storage output.toCStorageRef), ()⟩))))))) =
      (fun entry => record (oracles := oracles) wire qubit output operations services entry.1
        entry.2) := by
    funext entry
    exact congrArg
      (fun value : (CShape.finite (ctx.quantumLayout.wire wire).dimension).Value =>
        (show Store ctx × (services.HiddenState ×
        (History × (circuit (oracles := oracles) wire qubit output operations services
          allowAllocation).Path)) from
          (entry.1.1.write output (.finite entry.2),
            (entry.1.2.1, (entry.1.2.2, ((), (entry.2, ⟨value, ()⟩)))))))
      (Store.read_write_same entry.1.1 output (.finite entry.2))
  have updated := congrArg (fun update =>
    ((ExecutionState.measureZ
      (state.applyUnitary fun _ => UnitaryOperator.prodTensor
        ((hadamard wire qubit).matrix environment.quantum) (1 : UnitaryOperator Reference))
      (fun basis : (Register.prod ctx.register Reference).Index => basis.1 wire)).applyUnitary
        fun entry => UnitaryOperator.prodTensor
          (QuditShift.operator ctx.quantumLayout wire (-entry.2)) (1 : UnitaryOperator
            Reference)).mapClassical update) readBack
  refine Eq.trans ?_ updated
  congr 1
  exact Subsingleton.elim _ _

end

end QuantumAlg.EncodedBit.MeasuredUncompute
