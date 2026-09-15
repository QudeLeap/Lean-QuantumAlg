/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Oracle.UnitarySource
import all QuantumAlg.Components.Oracle.UnitarySource
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Components.Control

/-!
# A supplied unitary with one actual leading control

The source query is placed after physical system zero and structurally
controlled by that system. Its native label is derived from the original
query, as in the eigenvalue kickback circuit [CEMM98, cemm6.tex:140-166].
-/

namespace QuantumAlg.UnitarySource

noncomputable section

/-- The actual controlled source query on the complete control/input word. -/
def controlledProgram {width : Nat} (unitary : UnitaryOperator (Qubits width)) :
    UnitaryCircuit (Qubits (1 + width)) :=
  let shifted := UnitaryCircuit.shiftPhysicalIdx 1 (program unitary)
  UnitaryCircuit.controlQubitsAt [0] shifted
    { left_nodup := by simp
      right_nodup := shifted.physical_idx_nodup
      disjoint := by simp [shifted, UnitaryCircuit.shiftPhysicalIdx] }
    (1 : Fin 2)

theorem controlledProgram_matrix {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) :
    (controlledProgram unitary).matrix = UnitaryOperator.controlledQubits unitary := by
  simp [controlledProgram, UnitaryOperator.controlledQubits, program_matrix]

theorem controlledProgram_physicalIdx {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) :
    (controlledProgram unitary).physical_idx = List.range (1 + width) := by
  change [0] ++ (List.range width).map (fun wire => 1 + wire) = _
  simpa [Nat.add_comm, Nat.succ_eq_add_one] using
    (List.range_succ_eq_map : List.range (width + 1) =
      0 :: (List.range width).map Nat.succ).symm

theorem controlledProgram_events {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) :
    (controlledProgram unitary).eventCost =
      ResourcePool.singleton (controlledEvent width) := by
  rfl

theorem controlledProgram_depth {width : Nat}
    (unitary : UnitaryOperator (Qubits width)) :
    (controlledProgram unitary).evaluatedEventDepth (fun _ => 1) = 1 := by
  rfl

end

end QuantumAlg.UnitarySource
