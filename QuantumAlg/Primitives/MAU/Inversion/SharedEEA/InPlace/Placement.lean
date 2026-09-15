/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.InPlace.Forward

/-!
# Physical containment of the complete in-place shared-EEA forward

Every actual instruction remains inside the original two shared words
and small auxiliary fields [LYL+26, sec_EEA/sub_regshare.tex:16-26]. The
proof follows the emitted sequence, finite arithmetic selectors, actual
address placements, and repetitions, including the complete decoder and
real output-port gates. It does not infer physical containment from the
matrix dimension or replace a physical port permutation by a basis cast.

This inclusion permits the same full forward and dagger to be placed
beside a spectator word and to exchange which actual large workspace is
used, as in [LYL+26, sec_point_add/sec_point_add.tex:51-79].
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.InPlacePlacement

noncomputable section

open EncodedBit

private abbrev Within (width : Nat) (body : UnitaryCircuit (Qubits (encoding width).width)) :=
  body.physical_idx ⊆ List.range (encoding width).width

private theorem control_place (width : Nat)
    (body : UnitaryCircuit (Qubits (encoding width).width)) (within : Within width body) :
    Within width (ControlPlacement.place width body) := by
  change (ControlPlacement.place width body).physical_idx ⊆ _
  rw [ControlPlacement.place_physical]
  intro wire present
  obtain ⟨old, oldPresent, rfl⟩ := List.mem_map.mp present
  have oldWithin := List.mem_range.mp (within oldPresent)
  apply List.mem_range.mpr
  change Equiv.swap (phase2Bit width).wire.val (controlBit width).wire.val old < _
  rw [Equiv.swap_apply_def]
  split_ifs
  · exact (controlBit width).wire.isLt
  · exact (phase2Bit width).wire.isLt
  · exact oldWithin

private theorem clock (width : Nat) : Within width (ExtendedClockIncrement.program width) := by
  change (ExtendedClockIncrement.program width).physical_idx ⊆ _
  rw [ExtendedClockIncrement.program_physical]
  exact List.Subset.refl _

private theorem left_pair (width : Nat) : Within width (ControlledShift.leftProgram width) :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (control_place width _ (GateSpec.programList_physical_idx_subset_range _))
    (control_place width _ (clock width))

private theorem right_pair (width : Nat) : Within width (ControlledShift.rightProgram width) :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (control_place width _ (GateSpec.programList_physical_idx_subset_range _))
    (UnitaryCircuit.dagger_physical_idx_subset _ (control_place width _ (clock width)))

private theorem guarded (width : Nat) (selected : Bool) :
    Within width (GuardedShift.program width selected) := by
  have first : Within width (GuardedShift.firstProgram width selected) :=
    UnitaryCircuit.seq_physical_idx_subset _ _
      (GateSpec.programList_physical_idx_subset_range _)
      (UnitaryCircuit.seq_physical_idx_subset _ _ (left_pair width)
        (GateSpec.programList_physical_idx_subset_range _))
  have last : Within width (GuardedShift.lastProgram width selected) :=
    UnitaryCircuit.seq_physical_idx_subset _ _
      (GateSpec.programList_physical_idx_subset_range _)
      (UnitaryCircuit.seq_physical_idx_subset _ _
        (UnitaryCircuit.seq_physical_idx_subset _ _ (right_pair width) (right_pair width))
        (GateSpec.programList_physical_idx_subset_range _))
  exact UnitaryCircuit.seq_physical_idx_subset _ _ first last

private theorem selector_body {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (operation : ArithmeticWindowProgram.Operation) (coefficient : Bool) :
    Within width (ArithmeticSelector.controlledBody window operation coefficient) := by
  cases coefficient with
  | false =>
    change (ArithmeticWindowControl.program window operation).physical_idx ⊆ _
    rw [ArithmeticWindowControl.program, ArithmeticWindowPlacement.place_physical]
    exact List.Subset.refl _
  | true =>
    change (CoefficientWindowProgram.controlledProgram window operation).physical_idx ⊆ _
    rw [CoefficientWindowProgram.controlledProgram_physical]
    exact List.Subset.refl _

private theorem selector {width : Nat} (window : ArithmeticWindowRegisters.Window width)
    (operation : ArithmeticWindowProgram.Operation) (coefficient : Bool)
    (selected : ArithmeticSelectionKey.Key width
      (ArithmeticWindowPreservation.readsSign operation)) :
    Within width (ArithmeticSelector.program window operation coefficient selected) :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (GateSpec.programList_physical_idx_subset_range _)
    (UnitaryCircuit.seq_physical_idx_subset _ _ (selector_body window operation coefficient)
      (GateSpec.programList_physical_idx_subset_range _))

private theorem instruction (width : Nat) (instruction : ArithmeticInstruction.Instruction)
    (selected : ArithmeticSelectionKey.Key width (ArithmeticInstruction.includeSign instruction)) :
    Within width (ArithmeticInstruction.program width instruction selected) := by
  unfold ArithmeticInstruction.program
  split
  · cases choice : ArithmeticInstruction.selectedWindow instruction selected with
    | none => exact List.Subset.refl _
    | some window => exact selector window _ _ selected
  · exact List.Subset.refl _

private theorem arithmetic_list (width : Nat) (instruction : ArithmeticInstruction.Instruction)
    (indices : List (ArithmeticSelectionKey.Key width
      (ArithmeticInstruction.includeSign instruction))) :
    Within width (ArithmeticSchedule.listProgram width instruction indices) := by
  induction indices with
  | nil => exact List.Subset.refl _
  | cons selected rest inductionHypothesis =>
    exact UnitaryCircuit.seq_physical_idx_subset _ _
      (InPlacePlacement.instruction width instruction selected) inductionHypothesis

private theorem arithmetic (width : Nat) (instruction : ArithmeticInstruction.Instruction) :
    Within width (ArithmeticSchedule.program width instruction) :=
  arithmetic_list width instruction _

private theorem remainder (width : Nat) : Within width (ArithmeticBlocks.remainderProgram width) :=
  UnitaryCircuit.seq_physical_idx_subset _ _ (arithmetic width .remainderSubtract)
    (UnitaryCircuit.seq_physical_idx_subset _ _ (GateSpec.programList_physical_idx_subset_range _)
      (arithmetic width .remainderAddback))

private theorem coefficient (width : Nat) :
    Within width (ArithmeticBlocks.coefficientProgram width) :=
  UnitaryCircuit.seq_physical_idx_subset _ _ (arithmetic width .coefficientSubtract)
    (UnitaryCircuit.seq_physical_idx_subset _ _ (GateSpec.programList_physical_idx_subset_range _)
      (arithmetic width .coefficientAdd))

private theorem quotient (width : Nat) : Within width (PhaseQuotient.program width) := by
  have body : Within width (PhaseQuotient.bodyProgram width) :=
    UnitaryCircuit.seq_physical_idx_subset _ _
      (GateSpec.programList_physical_idx_subset_range _)
      (UnitaryCircuit.seq_physical_idx_subset _ _
        (QuotientIncrement.program_physical_idx_subset width)
        (GateSpec.programList_physical_idx_subset_range _))
  exact UnitaryCircuit.seq_physical_idx_subset _ _
    (GateSpec.programList_physical_idx_subset_range _)
    (UnitaryCircuit.seq_physical_idx_subset _ _ body
      (GateSpec.programList_physical_idx_subset_range _))

private theorem signQuotient (width : Nat) : Within width (SignQuotient.program width) :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (GateSpec.programList_physical_idx_subset_range _) (quotient width)

/-- All eight actual blocks remain inside the same original full source frame. -/
theorem microstep_within (width : Nat) (enough : 2 ≤ width.size) :
    (NativeMicrostep.program width enough).physical_idx ⊆ List.range (encoding width).width :=
  UnitaryCircuit.seq_physical_idx_subset _ _ (guarded width false)
    (UnitaryCircuit.seq_physical_idx_subset _ _ (remainder width)
      (UnitaryCircuit.seq_physical_idx_subset _ _ (signQuotient width)
        (UnitaryCircuit.seq_physical_idx_subset _ _ (coefficient width)
          (UnitaryCircuit.seq_physical_idx_subset _ _ (guarded width true)
            (UnitaryCircuit.seq_physical_idx_subset _ _
              (GateSpec.programList_physical_idx_subset_range _)
              (UnitaryCircuit.seq_physical_idx_subset _ _
                (GateSpec.programList_physical_idx_subset_range _)
                (GateSpec.programList_physical_idx_subset_range _)))))))

private theorem fold_source (modulus : Nat) :
    (FoldSourceProgram.program modulus).physical_idx ⊆
      List.range (FoldSourceProgram.wordWidth modulus + 2) := by
  have comparison : (Addition.Gidney.comparisonProgram (FoldSourceProgram.wordWidth modulus)
      (FoldSourceProgram.comparisonPivot modulus)).physical_idx ⊆
        List.range (FoldSourceProgram.wordWidth modulus + 2) := by
    rw [Addition.Gidney.gidneyComparison_physical]
    exact List.Subset.refl _
  exact UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _ comparison
      (OutputCorrectionFocus.flag_range (FoldSourceProgram.wordWidth modulus)))
    (Addition.Gidney.gidneyBiFlip_physical_range
      (FoldSourceProgram.wordWidth modulus) (FoldSourceProgram.reflectionPivot modulus))

private theorem initial (modulus : Nat) : Within modulus.size (InitialFrame.program modulus) := by
  have physical := FoldComparisonPlacement.placeFocus_physical modulus.size
    (FoldComparisonFocus.place (FoldSourceProgram.wordWidth modulus)
      (FoldSourceProgram.program modulus))
    (FoldComparisonFocus.place_physical_range (FoldSourceProgram.wordWidth modulus) _
      (fold_source modulus))
  have fold : Within modulus.size (FoldProgram.program modulus) := by
    intro wire present
    exact physical ▸ present
  exact UnitaryCircuit.seq_physical_idx_subset _ _ fold
    (GateSpec.programList_physical_idx_subset_range _)

private theorem native (modulus : Nat) (nontrivial : 1 < modulus) :
    Within modulus.size (NativeSchedule.program modulus nontrivial) :=
  UnitaryCircuit.seq_physical_idx_subset _ _ (initial modulus)
    (UnitaryCircuit.iterate_physical_idx_subset _ _
      (microstep_within modulus.size (PredicateLayout.modulus_length_width modulus nontrivial)))

private theorem decoder_list (width : Nat) (indices : List (Fin (width.size + 2))) :
    Within width (ClockDecode.sequence width indices) := by
  induction indices with
  | nil => exact GateSpec.programList_physical_idx_subset_range _
  | cons index rest inductionHypothesis =>
    exact UnitaryCircuit.seq_physical_idx_subset _ _
      (UnitaryCircuit.iterate_physical_idx_subset _ _
        (GateSpec.programList_physical_idx_subset_range _)) inductionHypothesis

/-- The fixed forward, full decoder, and coefficient correction share one physical frame. -/
theorem corrected_within (modulus : Nat) (nontrivial : 1 < modulus) :
    (CorrectedSchedule.program modulus nontrivial).physical_idx ⊆
      List.range (encoding modulus.size).width :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _ (native modulus nontrivial)
      (decoder_list modulus.size _))
    (by rw [OutputCorrection.program_physical]; exact List.Subset.refl _)

/-- The complete in-place forward needs no address outside its original shared frame. -/
theorem program_within (modulus : Nat) (nontrivial : 1 < modulus) :
    (InPlaceForward.program modulus nontrivial).physical_idx ⊆
      List.range (encoding modulus.size).width :=
  UnitaryCircuit.seq_physical_idx_subset _ _
    (GateSpec.programList_physical_idx_subset_range _)
    (UnitaryCircuit.seq_physical_idx_subset _ _ (corrected_within modulus nontrivial)
      (OutputPortProgram.program_physical_range modulus))

/-- The same complete dagger has identical physical containment, including its retained history. -/
theorem dagger_within (modulus : Nat) (nontrivial : 1 < modulus) :
    (InPlaceForward.program modulus nontrivial).dagger.physical_idx ⊆
      List.range (encoding modulus.size).width :=
  UnitaryCircuit.dagger_physical_idx_subset _ (program_within modulus nontrivial)

end

end QuantumAlg.MAU.Inversion.SharedEEA.InPlacePlacement
