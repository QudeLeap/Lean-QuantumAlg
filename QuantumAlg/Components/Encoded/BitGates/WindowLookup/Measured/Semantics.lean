/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Measured.Circuit
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Parity.Semantics
import all QuantumAlg.Core.Execution.Measurement.Sequence.Matrix
import all QuantumAlg.Core.Execution.Selected.Store

/-!
# Exact instrument of the actual parallel word measurement and reset

All H gates precede the actual chronological MZ writes. The paid native
packing instruction reads those real finite cells; its actual final Store
selects the X layer on those same physical result systems. Complete incoming
Store/history fibers and arbitrary external reference blocks remain explicit.
-/

namespace QuantumAlg.EncodedBit.WindowLookup

open Execution

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {oracles : OracleModel} {services : ClassicalOracleModel}
  {width : Nat}

/-- The real final Store after the named outcome writes and paid packing instruction. -/
def measuredWordFinalStore (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width) (output : Fin width → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits width)) (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path) : Store ctx :=
  (Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := oracles)
    (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
    (resultReadouts physical sameWires target output) store path).applyOp (resultPackOp output mask)

/-- The actual stored-mask selected physical X correction for this real original Store and path. -/
def measuredWordCorrection (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (store : Store ctx)
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path) :
    UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout :=
  unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
    (wordXProgram physical oracles target distinct
      (resultConstant ((measuredWordFinalStore (oracles := oracles) (services := services)
        physical sameWires target output mask store path).read (.storage mask.toCStorageRef))))

/-- Every old record, actual measured outcome, packed value and stored branch read is retained. -/
def measuredWordRecord (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    {History : Type} (entry : Store ctx × (services.HiddenState × History))
    (path : (Circuit.measurementSequence (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
      (resultReadouts physical sameWires target output)).Path) :
    Store ctx × (services.HiddenState × (History ×
      (measuredResetWordCircuit (oracles := oracles) (services := services)
        physical sameWires target distinct output mask).Path)) :=
  let measured := Circuit.writeMeasurementPath (gates := AlgorithmGate.model) (oracles := oracles)
    (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
    (resultReadouts physical sameWires target output) entry.1 path
  let packed := MaskParity.instructionStep (oracles := oracles) (services := services)
    (resultPackOp output mask) measured
  (packed.1, (entry.2.1, (entry.2.2,
    ((), (path, (packed.2, ⟨packed.1.read (.storage mask.toCStorageRef), ()⟩))))))

private lemma resultPack_execute (output : Fin width → CWriteRef ctx (.finite 2))
    (mask : CWriteRef ctx (.bits width))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (MaskParity.instruction (resultPackOp output mask)).execute environment Reference state =
      state.mapClassical (fun entry =>
        let result := MaskParity.instructionStep (oracles := oracles) (services := services)
          (resultPackOp output mask) entry.1
        (result.1, (entry.2.1, (entry.2.2, result.2)))) :=
  Circuit.execute_classical_mapClassical environment
    (BitWord.application (resultPackOp output mask))
    (resultPackOp output mask).eval (BitWord.bitWord_application_evaluate _) Reference state

/-- Full actual word instrument, with real packing/branch reads on each intermediate Store. -/
lemma measuredResetWordCircuit_execute (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (target : Word encoding width)
    (distinct : Function.Injective (fun index => (target.bit index).wire))
    (output : Fin width → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits width))
    (environment : (ExecutionModel.quantum AlgorithmGate.model oracles BitWord.model
      services).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (measuredResetWordCircuit physical sameWires target distinct output mask).execute
        environment Reference state =
      ((ExecutionState.measureZ
        (state.applyUnitary fun _ => UnitaryOperator.prodTensor
          ((unitaryOfEqualWires physical.toQuantum ctx.quantumLayout sameWires
            (wordHadamardProgram physical oracles target distinct)).matrix environment.quantum)
          (1 : UnitaryOperator Reference))
        (fun basis : (Register.prod ctx.register Reference).Index =>
          Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := oracles)
            (operations := BitWord.model) (classicalOracles := services) (allowAllocation := false)
            (resultReadouts physical sameWires target output) basis.1)).applyUnitary
          fun entry => UnitaryOperator.prodTensor
            ((measuredWordCorrection (services := services) physical sameWires target distinct
              output mask entry.1.1 entry.2).matrix environment.quantum)
            (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
              measuredWordRecord physical sameWires target distinct output mask
                entry.1 entry.2) := by
  unfold measuredResetWordCircuit
  rw [Circuit.execute_seq, Circuit.execute_unitary, Circuit.execute_seq,
    Circuit.measurementSequence_execute_joint, Circuit.execute_seq, resultPack_execute,
    Circuit.selectedUnitary_execute]
  simp only [State.mapHistory, ExecutionState.mapClassical_measureZ,
    ExecutionState.applyUnitary_mapClassical, ExecutionState.executionState_mapClassical_comp,
    Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.EncodedBit.WindowLookup
