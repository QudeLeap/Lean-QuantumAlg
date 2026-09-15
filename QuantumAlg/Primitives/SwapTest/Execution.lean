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
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Complete elementary SWAP-test execution

Prepare the one leading control, execute the literal gate list, and write the
actual Z outcome to the retained binary cell. The original two owned input
words and the control all remain in Output [BCWdW01, main.tex:287-328].
-/

namespace QuantumAlg.SwapTest

noncomputable section

open Execution

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
    UnitaryCircuit (HadamardTest.prepared (width + width)).register :=
  UnitaryCircuit.reindex (OwnedQubitPrefix.basisEquiv 1 (width + width)).symm
    (sourceCircuit width)

theorem nativeProgram_placement (width : Nat) :
    (nativeProgram width).physical_idx = (HadamardTest.prepared (width + width)).physicalIdx := by
  change (sourceCircuit width).physical_idx = _
  rw [sourceCircuit_physicalIdx, HadamardTest.prepared, OwnedQubitPrefix.post_physicalIdx]

def beforeMeasurement (width : Nat) : Circuit (pre width) (post width) :=
  .seq (OwnedQubitPrefix.prepareCode 1 (width + width))
    (.seq (.unitary (nativeProgram width) (nativeProgram_placement width))
      (.retain (HadamardTest.prepared (width + width)) ⟨2⟩ (.finite 2)
        (HadamardTest.resultFresh (width + width))))

def code (width : Nat) : Circuit (pre width) (post width) :=
  .seq (beforeMeasurement width) (HadamardTest.readoutCode (width + width))

def run (width : Nat) : AlgorithmRun (pre width) (post width) (.finite 2) where
  code := code width
  output := Output.all (post width)
    (.read (.storage (HadamardTest.resultRef (width + width)).toCStorageRef))

/-- Only the complete native run is stored in the public algorithm. -/
public def algorithm (width : Nat) : Algorithm .quantum (pre width) (post width) (.finite 2) :=
  ⟨run width⟩

/-- Native and abstract source operators coincide in the exact actual physical coordinates. -/
theorem nativeProgram_matrix (width : Nat) :
    (nativeProgram width).matrix =
      (HadamardTest.nativeProgram (swapRegistersOp width)).matrix := by
  simp only [nativeProgram, HadamardTest.nativeProgram, UnitaryCircuit.reindex_matrix,
    sourceCircuit_matrix, HadamardTest.sourceCircuit_matrix]
  rfl

private theorem nativeProgram_execute (width : Nat) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State (HadamardTest.prepared (width + width)) Reference History) :
    state.unitary (nativeProgram width) =
      state.unitary (HadamardTest.nativeProgram (swapRegistersOp width)) := by
  unfold State.unitary
  rw [nativeProgram_matrix]

/-- The complete quantum/classical state equals the source experiment; actual event ledgers
are derived separately from the elementary program. -/
theorem code_execute (width : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre width) Reference History) :
    (code width).execute Reference state =
      (HadamardTest.code (swapRegistersOp width)).execute Reference state := by
  simp only [code, beforeMeasurement, HadamardTest.code, HadamardTest.beforeMeasurement,
    Circuit.execute_seq, Circuit.execute_unitary, nativeProgram_execute]
  congr 1

end

end QuantumAlg.SwapTest
