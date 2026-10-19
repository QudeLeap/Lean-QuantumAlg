/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Primitives.SwapTest.Construction
import all QuantumAlg.Primitives.HadamardTest.Construction
import all QuantumAlg.Primitives.HadamardTest.Execution
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix.Coordinates
import all QuantumAlg.Core.Execution.Measurement.Sequence
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Complete elementary SWAP-test execution

Prepare the one leading control, execute the literal gate list, and write the
actual Z outcome to the retained binary cell. The original two owned input
words and the control all remain in Output [BCWdW01, main.tex:287-329].
-/

namespace QuantumAlg.SwapTest

noncomputable section

open Execution

/-- Default native operations with no quantum or classical oracle access. -/
public abbrev model : ExecutionModel := .quantum AlgorithmGate.model .empty

/-- The two complete supplied owned words, before the internal control is prepared. -/
@[reducible] public def pre (width : Nat) : RuntimeCtx .quantum :=
  HadamardTest.pre (width + width)

/-- Both original words, the prepared control, and the actual binary result remain live. -/
@[reducible] public def post (width : Nat) : RuntimeCtx .quantum :=
  HadamardTest.post (width + width)

/-- The supplied pair has its actual ordered binary basis labels in this public input frame. -/
public def inputBasisEquiv (width : Nat) :
    (pre width).register.Index ≃ (Qubits (width + width)).Index :=
  HadamardTest.inputBasisEquiv (width + width)

def nativeProgram (width : Nat) :
    UnitaryCircuit AlgorithmGate.model .empty
      (HadamardTest.prepared (width + width)).quantumLayout :=
  Execution.unitaryOfEqualWires (Gate.ControlledRegisterSwap.layout width)
    (HadamardTest.prepared (width + width)).quantumLayout
    (OwnedQubitPrefix.post_canonical_wires 1 (width + width)) (sourceCircuit width)

def beforeMeasurement (width : Nat) : Circuit model (pre width) (post width) :=
  .seq (OwnedQubitPrefix.prepareCode AlgorithmGate.model .empty 1 (width + width))
    (.seq (.unitary (nativeProgram width))
      (.retain (model := model) (HadamardTest.prepared (width + width)) ⟨2⟩ (.finite 2)
        (HadamardTest.resultFresh (width + width))))

def readoutCode (width : Nat) : Circuit model (post width) (post width) :=
  Circuit.measurementSequence [HadamardTest.readout (width + width)]

def code (width : Nat) : Circuit model (pre width) (post width) :=
  .seq (beforeMeasurement width) (readoutCode width)

def run (width : Nat) : AlgorithmRun model (pre width) (post width) (.finite 2) where
  code := code width
  output := Output.all (post width)
    (.read (.storage (HadamardTest.resultRef (width + width)).toCStorageRef))

lemma run_output_listing (width : Nat) :
    (run width).output.listing = (post width).keys := rfl

/-- Native and abstract source operators coincide in the exact actual physical coordinates. -/
lemma nativeProgram_matrix (width : Nat) (actual : model.Environment) :
    (nativeProgram width).matrix actual.quantum =
      (HadamardTest.nativeProgram (width + width)).matrix
        (UnitarySource.interpretation (swapRegistersOp width) true) := by
  rw [HadamardTest.nativeProgram_matrix]
  have physical : (sourceCircuit width).matrix actual.quantum =
      UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv (1 + (width + width))).symm
        (swapTest width) := by
    rw [← sourceCircuit_matrix]
    exact (UnitaryOperator.unitaryOperator_reindex_cancel
      (QuantumSignature.qubitsIndexEquiv (1 + (width + width)))
      ((sourceCircuit width).matrix actual.quantum)).symm
  rw [nativeProgram, Execution.unitaryOfEqualWires_matrix, physical,
    ← OwnedQubitPrefix.canonicalBasisEquiv_eq_basisEquiv]
  exact UnitaryOperator.unitaryOperator_reindex_trans _ _ _

private lemma preparation_execute (width : Nat) (actual : model.Environment) {Reference :
    Register}
    {History : Type} [Fintype History]
    (state : State (pre width) Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    (OwnedQubitPrefix.prepareCode AlgorithmGate.model .empty 1 (width + width)).execute actual
        Reference state =
      (OwnedQubitPrefix.prepareCode AlgorithmGate.model
        (UnitarySource.model (width + width) true) 1 (width + width)).execute
          (HadamardTest.environment (swapRegistersOp width))
          Reference state := rfl

private lemma nativeProgram_execute (width : Nat) (actual : model.Environment) {Reference :
    Register}
    {History : Type} [Fintype History]
    (state : State (HadamardTest.prepared (width + width)) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) :
    (Circuit.unitary (allowAllocation := true)
      (operations := .empty) (classicalOracles := .empty)
      (nativeProgram width)).execute actual Reference state =
      (Circuit.unitary (allowAllocation := true)
        (operations := .empty) (classicalOracles := .empty)
        (HadamardTest.nativeProgram (width + width))).execute (HadamardTest.environment
          (swapRegistersOp width)) Reference state := by
  rw [Circuit.execute_unitary, Circuit.execute_unitary, nativeProgram_matrix]
  rfl

private lemma beforeMeasurement_execute (width : Nat) (actual : model.Environment) {Reference :
    Register}
    {History : Type} [Fintype History]
    (state : State (pre width) Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    (beforeMeasurement width).execute actual Reference state =
      (HadamardTest.beforeMeasurement (width + width)).execute (HadamardTest.environment
        (swapRegistersOp width)) Reference state := by
  simp only [beforeMeasurement, HadamardTest.beforeMeasurement, Circuit.execute_seq,
    Circuit.execute_retain]
  rw [nativeProgram_execute, preparation_execute]
  rfl

private lemma readout_execute (width : Nat) (actual : model.Environment) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (post width) Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    (readoutCode width).execute actual Reference state =
      (HadamardTest.readoutCode (width + width)).execute (HadamardTest.environment
        (swapRegistersOp width)) Reference state := rfl

/-- The complete quantum/classical state equals the source experiment; actual event ledgers
are derived separately from the elementary program. -/
lemma code_execute (width : Nat) (actual : model.Environment) {Reference : Register} {History :
    Type} [Fintype History]
    (state : State (pre width) Reference (ClassicalOracleModel.empty.HiddenState × History)) :
    (code width).execute actual Reference state =
      (HadamardTest.code (width + width)).execute (HadamardTest.environment (swapRegistersOp
        width)) Reference state := by
  simp only [code, HadamardTest.code, Circuit.execute_seq]
  exact congrArg
    (fun result => result.mapHistory
      (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))))
    ((congrArg ((readoutCode width).execute actual Reference)
      (beforeMeasurement_execute width actual state)).trans (readout_execute width actual _))

end

end QuantumAlg.SwapTest
