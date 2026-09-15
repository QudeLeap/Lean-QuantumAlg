/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit
import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Primitives.MAU.Inversion.Layout
import all QuantumAlg.Primitives.MAU.Inversion.MK.Readout.Trace

/-! # Physical footprint of the fixed-round Montgomery--Kaliski circuit -/

section

namespace QuantumAlg.MAU.Inversion.MK

noncomputable section

/-- The original-active latch stays inside its path-work carrier. -/
theorem fullRoundPathWorkOriginalActiveLatchProgram_physical_idx_subset_range
    (tail counterWidth : Nat) :
    (fullRoundPathWorkOriginalActiveLatchProgram tail counterWidth).physical_idx ⊆
      List.range
        (registersWithFullRoundPathWorkEncoding tail.succ counterWidth).width := by
  unfold fullRoundPathWorkOriginalActiveLatchProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- Adding the clean control-work bit preserves the original-active latch
footprint certificate. -/
theorem fullRoundPathControlWorkOriginalActiveLatchProgram_physical_idx_subset_range
    (tail counterWidth : Nat) :
    (fullRoundPathControlWorkOriginalActiveLatchProgram
      tail counterWidth).physical_idx ⊆
      List.range
        (registersWithFullRoundPathControlWorkEncoding
          tail.succ counterWidth).width := by
  unfold fullRoundPathControlWorkOriginalActiveLatchProgram
    liftFullRoundPathWorkProgramToControlWork
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  exact fullRoundPathWorkOriginalActiveLatchProgram_physical_idx_subset_range
    tail counterWidth

/-- The active-false padding gate list stays in its detector/counter carrier. -/
theorem detectorCounterActiveFalseControlledInactivePaddingProgram_physical_idx_subset_range
    (tail counterWidth : Nat) :
    (detectorCounterActiveFalseControlledInactivePaddingProgram
      tail counterWidth).physical_idx ⊆
      List.range
        (registersWithDetectorCounterWorkEncoding
          tail.succ counterWidth).width := by
  unfold detectorCounterActiveFalseControlledInactivePaddingProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- Inserting coefficient-adder work preserves the active-false padding
footprint certificate. -/
theorem fullRoundWorkActiveFalseControlledInactivePaddingProgram_physical_idx_subset_range
    (tail counterWidth : Nat) :
    (fullRoundWorkActiveFalseControlledInactivePaddingProgram
      tail counterWidth).physical_idx ⊆
      List.range
        (registersWithFullRoundWorkEncoding tail.succ counterWidth).width := by
  unfold fullRoundWorkActiveFalseControlledInactivePaddingProgram
  apply UnitaryCircuit.insertMiddle_physical_idx_subset_range
  exact
    detectorCounterActiveFalseControlledInactivePaddingProgram_physical_idx_subset_range
      tail counterWidth

/-- Adding path and control-work bits preserves the active-false padding
footprint certificate. -/
theorem fullRoundPathControlWorkActiveFalseInactivePaddingProgram_physical_idx_subset_range
    (tail counterWidth : Nat) :
    (fullRoundPathControlWorkActiveFalseInactivePaddingProgram
      tail counterWidth).physical_idx ⊆
      List.range
        (registersWithFullRoundPathControlWorkEncoding
          tail.succ counterWidth).width := by
  unfold fullRoundPathControlWorkActiveFalseInactivePaddingProgram
    liftFullRoundWorkProgramToPathControlWork
    liftFullRoundPathWorkProgramToControlWork
    liftFullRoundWorkProgramToPathWork
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  exact
    fullRoundWorkActiveFalseControlledInactivePaddingProgram_physical_idx_subset_range
      tail counterWidth

end

end QuantumAlg.MAU.Inversion.MK

namespace QuantumAlg.MAU.Inversion.MK.Circuit

noncomputable section

/-- The route-history lift of the original-active latch stays in the fixed
round carrier. -/
theorem originalActiveLatchProgram_physical_idx_subset_range
    (tail counterWidth : Nat) :
    (originalActiveLatchProgram tail counterWidth).physical_idx ⊆
      List.range (encoding tail.succ counterWidth).width := by
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range
    (originalActiveLatchGates tail counterWidth)

/-- The route-history lift of inactive padding stays in the fixed-round
carrier. -/
theorem inactivePaddingProgram_physical_idx_subset_range
    (tail counterWidth : Nat) :
    (inactivePaddingProgram tail counterWidth).physical_idx ⊆
      List.range (encoding tail.succ counterWidth).width := by
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range
    (inactivePaddingGates tail counterWidth)

/-- The controlled active-only route stays in the fixed-round carrier. -/
theorem controlledActiveOnlyProgram_physical_idx_subset_range
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (historyIndex : Fin (2 * tail.succ)) (workIndex : Fin (counterWidth - 1)) :
    (controlledActiveOnlyProgram tail counterWidth comparisonIndex
      historyIndex workIndex).physical_idx ⊆
      List.range (encoding tail.succ counterWidth).width := by
  unfold controlledActiveOnlyProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The branch-residue cleanup gate list stays in the fixed-round carrier. -/
theorem branchResidueCleanupProgram_physical_idx_subset_range
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    (branchResidueCleanupProgram tail counterWidth roundIndex).physical_idx ⊆
      List.range (encoding tail.succ counterWidth).width := by
  unfold branchResidueCleanupProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The route-history spill gate stays in the fixed-round carrier. -/
theorem spillWorkingPathProgram_physical_idx_subset_range
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    (spillWorkingPathProgram tail counterWidth roundIndex).physical_idx ⊆
      List.range (encoding tail.succ counterWidth).width := by
  unfold spillWorkingPathProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The route-history reset gate stays in the fixed-round carrier. -/
theorem resetWorkingPathProgram_physical_idx_subset_range
    (tail counterWidth : Nat) (roundIndex : Fin (2 * tail.succ)) :
    (resetWorkingPathProgram tail counterWidth roundIndex).physical_idx ⊆
      List.range (encoding tail.succ counterWidth).width := by
  unfold resetWorkingPathProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- One fixed round remains inside its common physical carrier. -/
theorem roundProgram_physical_idx_subset_range
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) (roundIndex : Fin (2 * tail.succ)) :
    (roundProgram tail counterWidth comparisonIndex workIndex roundIndex).physical_idx ⊆
      List.range (encoding tail.succ counterWidth).width := by
  unfold roundProgram roundPrograms
  apply UnitaryCircuit.seq_physical_idx_subset
  · exact originalActiveLatchProgram_physical_idx_subset_range tail counterWidth
  · apply UnitaryCircuit.seq_physical_idx_subset
    · exact inactivePaddingProgram_physical_idx_subset_range tail counterWidth
    · apply UnitaryCircuit.seq_physical_idx_subset
      · exact controlledActiveOnlyProgram_physical_idx_subset_range
          tail counterWidth comparisonIndex roundIndex workIndex
      · apply UnitaryCircuit.seq_physical_idx_subset
        · exact branchResidueCleanupProgram_physical_idx_subset_range
            tail counterWidth roundIndex
        · apply UnitaryCircuit.seq_physical_idx_subset
          · exact spillWorkingPathProgram_physical_idx_subset_range
              tail counterWidth roundIndex
          · apply UnitaryCircuit.seq_physical_idx_subset
            · exact resetWorkingPathProgram_physical_idx_subset_range
                tail counterWidth roundIndex
            · simp [UnitaryCircuit.identity]

/-- A sequential fold of canonically contained fixed-round programs remains
inside its carrier. -/
private theorem foldrSeq_physical_idx_subset_range {n : Nat} :
    ∀ (programs : List (UnitaryCircuit (Qubits n))),
      (∀ program ∈ programs, program.physical_idx ⊆ List.range n) →
      (programs.foldr UnitaryCircuit.seq
        (UnitaryCircuit.identity (Qubits n) [] (by simp))).physical_idx ⊆
        List.range n
  | [], _ => by
      simp [UnitaryCircuit.identity]
  | program :: programs, contained => by
      apply UnitaryCircuit.seq_physical_idx_subset
      · exact contained program (by simp)
      · apply foldrSeq_physical_idx_subset_range programs
        intro next hnext
        exact contained next (by simp [hnext])

/-- The complete input-independent fixed-round Montgomery--Kaliski fold stays
inside its canonical carrier. -/
theorem foldProgram_physical_idx_subset_range
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    (foldProgram tail counterWidth comparisonIndex workIndex).physical_idx ⊆
      List.range (encoding tail.succ counterWidth).width := by
  unfold foldProgram
  apply foldrSeq_physical_idx_subset_range
  intro program hprogram
  rw [foldPrograms] at hprogram
  rcases List.mem_ofFn.mp hprogram with ⟨roundIndex, rfl⟩
  exact roundProgram_physical_idx_subset_range
    tail counterWidth comparisonIndex workIndex roundIndex

/-- Reversing the fixed-round fold preserves its physical carrier. -/
theorem foldInverseProgram_physical_idx_subset_range
    (tail counterWidth : Nat) (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    (foldInverseProgram tail counterWidth comparisonIndex workIndex).physical_idx ⊆
      List.range (encoding tail.succ counterWidth).width := by
  unfold foldInverseProgram
  exact UnitaryCircuit.dagger_physical_idx_subset _
    (foldProgram_physical_idx_subset_range tail counterWidth
      comparisonIndex workIndex)

end

end QuantumAlg.MAU.Inversion.MK.Circuit

end
