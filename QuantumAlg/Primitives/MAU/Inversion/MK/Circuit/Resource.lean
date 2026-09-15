/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit

/-! # Structural resource certificate for the fixed-round inversion circuit -/

section

namespace QuantumAlg.MAU.Inversion.MK.Circuit

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

private theorem dagger_eventCost {R : Register} (body : UnitaryCircuit R) :
    body.dagger.eventCost = body.eventCost := rfl

private theorem qfree_dagger {R : Register} {program : UnitaryCircuit R}
    (hprogram : QuantumSubroutineFree program) :
    QuantumSubroutineFree program.dagger := by
  intro label
  rw [dagger_eventCost]
  exact hprogram label

private theorem qfree_fullRoundPathWorkOriginalActiveLatch
    (tail counterWidth : Nat) :
    QuantumSubroutineFree
      (fullRoundPathWorkOriginalActiveLatchProgram tail counterWidth) := by
  intro label
  unfold fullRoundPathWorkOriginalActiveLatchProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_fullRoundPathControlWorkOriginalActiveLatch
    (tail counterWidth : Nat) :
    QuantumSubroutineFree
      (fullRoundPathControlWorkOriginalActiveLatchProgram
        tail counterWidth) := by
  unfold fullRoundPathControlWorkOriginalActiveLatchProgram
    liftFullRoundPathWorkProgramToControlWork
  apply qfree_prodLeft
  exact qfree_fullRoundPathWorkOriginalActiveLatch tail counterWidth

private theorem qfree_detectorCounterActiveFalseInactivePadding
    (tail counterWidth : Nat) :
    QuantumSubroutineFree
      (detectorCounterActiveFalseControlledInactivePaddingProgram
        tail counterWidth) := by
  intro label
  unfold detectorCounterActiveFalseControlledInactivePaddingProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_fullRoundWorkActiveFalseInactivePadding
    (tail counterWidth : Nat) :
    QuantumSubroutineFree
      (fullRoundWorkActiveFalseControlledInactivePaddingProgram
        tail counterWidth) := by
  unfold fullRoundWorkActiveFalseControlledInactivePaddingProgram
  apply qfree_insertMiddle
  exact qfree_detectorCounterActiveFalseInactivePadding tail counterWidth

private theorem qfree_fullRoundPathControlWorkActiveFalseInactivePadding
    (tail counterWidth : Nat) :
    QuantumSubroutineFree
      (fullRoundPathControlWorkActiveFalseInactivePaddingProgram
        tail counterWidth) := by
  unfold fullRoundPathControlWorkActiveFalseInactivePaddingProgram
    liftFullRoundWorkProgramToPathControlWork
    liftFullRoundPathWorkProgramToControlWork
    liftFullRoundWorkProgramToPathWork
  apply qfree_prodLeft
  apply qfree_prodLeft
  exact qfree_fullRoundWorkActiveFalseInactivePadding tail counterWidth

private theorem qfree_originalActiveLatch (tail counterWidth : Nat) :
    QuantumSubroutineFree (originalActiveLatchProgram tail counterWidth) := by
  intro label
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero
    (originalActiveLatchGates tail counterWidth) label

private theorem qfree_inactivePadding (tail counterWidth : Nat) :
    QuantumSubroutineFree (inactivePaddingProgram tail counterWidth) := by
  intro label
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero
    (inactivePaddingGates tail counterWidth) label

private theorem qfree_controlledActiveOnly
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ))
    (workIndex : Fin (counterWidth - 1)) :
    QuantumSubroutineFree
      (controlledActiveOnlyProgram tail counterWidth comparisonIndex
        historyIndex workIndex) := by
  intro label
  unfold controlledActiveOnlyProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_branchResidueCleanup
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    QuantumSubroutineFree
      (branchResidueCleanupProgram tail counterWidth roundIndex) := by
  intro label
  unfold branchResidueCleanupProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_spillWorkingPath
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    QuantumSubroutineFree
      (spillWorkingPathProgram tail counterWidth roundIndex) := by
  intro label
  unfold spillWorkingPathProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_resetWorkingPath
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    QuantumSubroutineFree
      (resetWorkingPathProgram tail counterWidth roundIndex) := by
  intro label
  unfold resetWorkingPathProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

private theorem qfree_round
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (roundIndex : Fin (2 * tail.succ)) :
    QuantumSubroutineFree
      (roundProgram tail counterWidth comparisonIndex workIndex roundIndex) := by
  unfold roundProgram roundPrograms
  exact qfree_seq (qfree_originalActiveLatch tail counterWidth) <|
    qfree_seq (qfree_inactivePadding tail counterWidth) <|
    qfree_seq
      (qfree_controlledActiveOnly tail counterWidth comparisonIndex
        roundIndex workIndex) <|
    qfree_seq (qfree_branchResidueCleanup tail counterWidth roundIndex) <|
    qfree_seq (qfree_spillWorkingPath tail counterWidth roundIndex) <|
    qfree_seq (qfree_resetWorkingPath tail counterWidth roundIndex)
      qfree_identity

private theorem qfree_foldrSeq {n : Nat} :
    ∀ (programs : List (UnitaryCircuit (Qubits n))),
      (∀ program ∈ programs, QuantumSubroutineFree program) →
      QuantumSubroutineFree
        (programs.foldr UnitaryCircuit.seq
          (UnitaryCircuit.identity (Qubits n) [] (by simp)))
  | [], _ => qfree_identity
  | program :: programs, hprograms => by
      apply qfree_seq
      · exact hprograms program (by simp)
      · apply qfree_foldrSeq programs
        intro later hlater
        exact hprograms later (by simp [hlater])

private theorem qfree_fold
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    QuantumSubroutineFree
      (foldProgram tail counterWidth comparisonIndex workIndex) := by
  unfold foldProgram
  apply qfree_foldrSeq
  intro program hprogram
  rw [foldPrograms] at hprogram
  rcases List.mem_ofFn.mp hprogram with ⟨roundIndex, rfl⟩
  exact qfree_round tail counterWidth comparisonIndex workIndex roundIndex

private theorem qfree_foldInverse
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    QuantumSubroutineFree
      (foldInverseProgram tail counterWidth comparisonIndex workIndex) := by
  unfold foldInverseProgram
  exact qfree_dagger (qfree_fold tail counterWidth comparisonIndex workIndex)

/-- The concrete fixed-round Montgomery--Kaliski fold is assembled only from
encoded-bit gate lists, structural lifts, and serial composition. -/
theorem foldProgram_quantumSubroutine_count_zero
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (label : QuantumAlg.Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
      (foldProgram tail counterWidth comparisonIndex workIndex).eventCost = 0 :=
  qfree_fold tail counterWidth comparisonIndex workIndex label

/-- Daggering the concrete fixed-round fold cannot introduce a
quantum-subroutine event. -/
theorem foldInverseProgram_quantumSubroutine_count_zero
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (label : QuantumAlg.Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
      (foldInverseProgram tail counterWidth comparisonIndex workIndex).eventCost = 0 :=
  qfree_foldInverse tail counterWidth comparisonIndex workIndex label

end

end QuantumAlg.MAU.Inversion.MK.Circuit

end
