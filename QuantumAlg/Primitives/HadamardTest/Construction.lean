/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.UnitarySource
public import QuantumAlg.Core.Base.Accounting.Context
import all QuantumAlg.Components.Oracle.UnitarySource
import all QuantumAlg.Primitives.HadamardTest.Basic
import all QuantumAlg.Core.Execution.Owned.Qubit.Prefix
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction

/-!
# The actual Hadamard-test source circuit and physical runtime frame

Two actual Hadamards surround one controlled source query. The input is owned
because this general test may change it; the fresh control is prepared by a
separate counted instruction. The runtime frame retains the control and the
entire input word [AJL06, qf2.tex:625-645].
-/

namespace QuantumAlg.HadamardTest

noncomputable section

open Execution

/-- Two literal Hadamards around the controlled source-unitary access. -/
def sourceCircuit {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    UnitaryCircuit (Qubits (1 + width)) :=
  (hadamardTestCircuit (UnitarySource.program unitary)).seq
    (UnitaryCircuit.identity (Qubits (1 + width)) (List.range (1 + width)) List.nodup_range)

/-- The actual source circuit has the registered Hadamard-test operator. -/
theorem sourceCircuit_matrix {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (sourceCircuit unitary).matrix = hadamardTest unitary := by
  change 1 * (hadamardTestCircuit (UnitarySource.program unitary)).matrix = _
  rw [one_mul, hadamardTestCircuit_matrix, UnitarySource.program_matrix]

/-- Every source query and both boundary gates are retained as native occurrences. -/
theorem sourceCircuit_eventTrace {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (sourceCircuit unitary).eventTrace =
      [.gate (.builtin "hadamard"), UnitarySource.controlledEvent width,
        .gate (.builtin "hadamard")] := by
  change (hadamardTestCircuit (UnitarySource.program unitary)).eventTrace ++ [] = _
  rw [List.append_nil, hadamardTestCircuit_eventTrace, UnitarySource.program_eventTrace]
  rfl

/-- The complete source/input register is the actual circuit footprint. -/
theorem sourceCircuit_physicalIdx {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (sourceCircuit unitary).physical_idx = List.range (1 + width) := by
  change UnitaryCircuit.unionPhysicalIdx
    (hadamardTestCircuit (UnitarySource.program unitary)).physical_idx
      (List.range (1 + width)) = _
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  have boundary : (hadamardTestHadamardLayer width).physical_idx ⊆ List.range (1 + width) := by
    intro index present
    change index ∈ [0] at present
    obtain rfl := List.mem_singleton.mp present
    simp
  have query : (hadamardTestControlledLayer (UnitarySource.program unitary)).physical_idx ⊆
      List.range (1 + width) := by
    intro index present
    change index ∈ [0] ++ (List.range width).map (fun wire => 1 + wire) at present
    rcases List.mem_append.mp present with atControl | atInput
    · obtain rfl := List.mem_singleton.mp atControl
      simp
    · obtain ⟨wire, within, rfl⟩ := List.mem_map.mp atInput
      exact List.mem_range.mpr (Nat.add_lt_add_left (List.mem_range.mp within) 1)
  exact UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _ boundary query) boundary

/-- The source word is supplied without a clean control or borrowed-restoration promise. -/
@[reducible] public def pre (width : Nat) : RuntimeCtx .quantum := OwnedQubitPrefix.pre 1 width

/-- The supplied input's actual ordered physical wires have their original binary labels. -/
public def inputBasisEquiv (width : Nat) :
    (pre width).register.Index ≃ (Qubits width).Index :=
  OwnedQubitPrefix.inputBasisEquiv 1 width

/-- The fresh actual control precedes the still-live owned input. -/
@[reducible] public def prepared (width : Nat) : RuntimeCtx .quantum :=
  OwnedQubitPrefix.post 1 width

/-- Source unitary execution in the actual preparation coordinates. -/
def nativeProgram {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    UnitaryCircuit (prepared width).register :=
  UnitaryCircuit.reindex (OwnedQubitPrefix.basisEquiv 1 width).symm (sourceCircuit unitary)

theorem nativeProgram_placement {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    (nativeProgram unitary).physical_idx = (prepared width).physicalIdx := by
  change (sourceCircuit unitary).physical_idx = (prepared width).physicalIdx
  rw [sourceCircuit_physicalIdx, prepared, OwnedQubitPrefix.post_physicalIdx]

end

end QuantumAlg.HadamardTest
