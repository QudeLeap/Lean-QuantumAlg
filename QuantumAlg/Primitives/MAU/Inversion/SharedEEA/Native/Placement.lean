/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.PreparedFrame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Control
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement

/-!
# Physical placement of the native shared-EEA control kernel

The source encoding orders the body before Ctrl. The prepared runtime orders
the newly allocated Ctrl before the old body. The position injection maps
every source system to its actual retained physical wire. Placement transports
the original native leaves and their exact event accounting.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.NativePlacement

noncomputable section

open ControlPreparation

private def positionValue (width index : Nat) : Nat :=
  if index < bodyWidth width then index + 1 else 0

private theorem before_count (width : Nat) :
    (before width).systemCount = bodyWidth width := by
  have wires := congrArg List.length (Execution.OwnedQubits.canonical_wires (bodyWidth width))
  simpa only [QuantumLayout.wires_length, RuntimeCtx.quantumLayout_wires,
    RuntimeCtx.systemCount, before] using wires.symm

theorem after_count (width : Nat) :
    (after width).systemCount = 1 + bodyWidth width := by
  have wires := congrArg List.length
    (RuntimeCtx.runtimeCtx_quantumWires_addOwnedLayout (before width)
      controlKey (controlLayout width) (control_fresh width) (control_disjoint width))
  simpa only [after, RuntimeCtx.systemCount, List.length_append,
    QuantumLayout.wires_length, before_count] using wires

/-- Source body positions follow the fresh Ctrl; the final source Ctrl is first. -/
def position (width : Nat) :
    Fin (encoding width).width ↪ Fin (after width).systemCount where
  toFun index := ⟨positionValue width index.val, by
    have within := index.isLt
    have complete := complete_width width
    rw [after_count]
    unfold positionValue
    split_ifs <;> omega⟩
  inj' := by
    intro left right same
    have values := congrArg Fin.val same
    have leftWithin := left.isLt
    have rightWithin := right.isLt
    have complete := complete_width width
    apply Fin.ext
    change positionValue width left.val = positionValue width right.val at values
    unfold positionValue at values
    split_ifs at values <;> omega

theorem position_dimensions (width : Nat) (index : Fin (encoding width).width) :
    ((QubitLayout.canonical (encoding width).width).toQuantum.wire index).dimension =
      ((after width).quantumLayout.wire (position width index)).dimension := by
  have qubit_wires {count : Nat} (layout : QubitLayout count)
      (wire : QuantumWire) (member : wire ∈ layout.toQuantum.wires) :
      wire.dimension = 2 := by
    rw [QuantumLayout.wires, List.mem_ofFn] at member
    obtain ⟨located, rfl⟩ := member
    rfl
  have member : ((after width).quantumLayout.wire (position width index)) ∈
      (after width).quantumWires := by
    rw [← RuntimeCtx.quantumLayout_wires]
    exact List.mem_ofFn.mpr ⟨position width index, rfl⟩
  have dimension : ((after width).quantumLayout.wire (position width index)).dimension =
      2 := by
    change ((after width).quantumLayout.wire (position width index)) ∈
      (controlLayout width).wires ++ (before width).quantumWires at member
    rcases List.mem_append.mp member with fresh | prior
    · exact qubit_wires (controlQubitLayout width) _ fresh
    · have old : ((after width).quantumLayout.wire (position width index)) ∈
          (Execution.OwnedQubits.context (bodyWidth width)).quantumLayout.wires := by
        simpa only [before, RuntimeCtx.quantumLayout_wires] using prior
      rw [← Execution.OwnedQubits.canonical_wires] at old
      exact qubit_wires (QubitLayout.canonical _) _ old
  have sourceDimension :
      ((QubitLayout.canonical (encoding width).width).toQuantum.wire index).dimension =
        2 := rfl
  exact sourceDimension.trans dimension.symm

/-- Every native predicate gate is placed at its matching retained physical system. -/
def program (width : Nat) (enough : 2 ≤ width.size) :
    UnitaryCircuit AlgorithmGate.model .empty (after width).quantumLayout :=
  UnitaryCircuit.placeAt
    (QubitLayout.canonical (encoding width).width).toQuantum
    (after width).quantumLayout (position width) (position_dimensions width)
    (NativeControl.program width enough)

theorem program_eventTrace (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventTrace = (NativeControl.program width enough).eventTrace :=
  UnitaryCircuit.placeAt_eventTrace _ _ _ _ _

theorem program_eventCost (width : Nat) (enough : 2 ≤ width.size) :
    (program width enough).eventCost = (NativeControl.program width enough).eventCost :=
  UnitaryCircuit.placeAt_eventCost _ _ _ _ _

end

end QuantumAlg.MAU.Inversion.SharedEEA.NativePlacement
