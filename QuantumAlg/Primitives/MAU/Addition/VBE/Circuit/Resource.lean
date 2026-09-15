/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Primitives.Arithmetic.BitSlice
import all QuantumAlg.Primitives.Arithmetic.Comparator
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Physical
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule.ZeroTestValue
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Util.ZModUnits
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.MAU.Addition.StructuredCircuit
import all QuantumAlg.Primitives.MAU.Addition.Physical

/-! # Structural resource certificate for the VBE modular adder -/

section

namespace QuantumAlg
namespace MAU.Addition
namespace VBECircuit

noncomputable section

private abbrev QuantumSubroutineFree {R : Register} (program : UnitaryCircuit R) : Prop :=
  ∀ label : QuantumAlg.Resource.QuantumSubroutineLabel,
    ResourcePool.count (.quantumSubroutine label) program.eventCost = 0

private theorem qfree_identity {R : Register} :
    QuantumSubroutineFree (UnitaryCircuit.identity R [] (by simp)) := by
  intro label
  rfl

private theorem qfree_seq {R : Register} {left right : UnitaryCircuit R}
    (hleft : QuantumSubroutineFree left)
    (hright : QuantumSubroutineFree right) :
    QuantumSubroutineFree (UnitaryCircuit.seq left right) := by
  intro label
  simp only [UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
    hleft label, hright label, Nat.zero_add]

private theorem qfree_prodLeft {m n : Nat}
    (program : UnitaryCircuit (Qubits m))
    (hprogram : QuantumSubroutineFree program) :
    QuantumSubroutineFree (UnitaryCircuit.prodLeft (n := n) program) := by
  intro label
  rw [UnitaryCircuit.prodLeft_eventCost]
  exact hprogram label

private theorem qfree_insertMiddle
    {leftWidth middleWidth rightWidth : Nat}
    (program : UnitaryCircuit (Qubits (leftWidth + rightWidth)))
    (hprogram : QuantumSubroutineFree program) :
    QuantumSubroutineFree
      (UnitaryCircuit.insertMiddle (middleWidth := middleWidth) program) := by
  intro label
  rw [UnitaryCircuit.insertMiddle_eventCost]
  exact hprogram label

private theorem qfree_activeAdderCore (n : Nat) :
    QuantumSubroutineFree (activeAdderCoreProgram n) := by
  intro label
  unfold activeAdderCoreProgram
  unfold PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumProgram
  unfold PlainAdder.Schedule.CarryWorkLayout.cleanCarrySumProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_activeAdder (n : Nat) :
    QuantumSubroutineFree (activeAdderProgram n) := by
  unfold activeAdderProgram activeAdderCarrierProgram
  apply qfree_prodLeft
  apply qfree_insertMiddle
  exact qfree_activeAdderCore n

private theorem qfree_activeAdderInverse (n : Nat) :
    QuantumSubroutineFree (activeAdderInverseProgram n) := by
  unfold activeAdderInverseProgram activeAdderInverseCarrierProgram
  apply qfree_prodLeft
  apply qfree_insertMiddle
  intro label
  unfold adderInverseCoreProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_sourceSwap (n : Nat) :
    QuantumSubroutineFree (sourceSwapProgram n) := by
  intro label
  unfold sourceSwapProgram EncodedBit.Word.swapProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_copyReductionFlag (n : Nat) :
    QuantumSubroutineFree (copyReductionFlagProgram n) := by
  intro label
  unfold copyReductionFlagProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_cleanupReductionFlag (n : Nat) :
    QuantumSubroutineFree (cleanupReductionFlagProgram n) := by
  intro label
  unfold cleanupReductionFlagProgram
  exact EncodedBit.GateSpec.program_quantumSubroutine_count_zero _ label

private theorem qfree_clearActiveModulus (n N : Nat) :
    QuantumSubroutineFree (clearActiveModulusProgram n N) := by
  intro label
  unfold clearActiveModulusProgram EncodedBit.Word.controlledXorConstantProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_restoreActiveModulus (n N : Nat) :
    QuantumSubroutineFree (restoreActiveModulusProgram n N) := by
  intro label
  unfold restoreActiveModulusProgram
    EncodedBit.Word.controlledXorConstantUnloadProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_modularAdd (n N : Nat) :
    QuantumSubroutineFree (modularAddProgram n N) := by
  intro label
  unfold modularAddProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

/-- The exact VBE compare/subtract/add-back circuit contains only encoded-bit
gates and structural lifts, so no quantum-subroutine event is present. -/
theorem modularAddProgram_quantumSubroutine_count_zero
    (n N : Nat) (label : QuantumAlg.Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
      (modularAddProgram n N).eventCost = 0 :=
  qfree_modularAdd n N label

end

end VBECircuit
end MAU.Addition
end QuantumAlg

end
