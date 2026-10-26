/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Program
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Boundary.Frame
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Copy.Positive
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement
import all QuantumAlg.Primitives.MAU.Addition.TTK.Placement.Subtraction
import all QuantumAlg.Components.Encoded.BitGates.WirePlacement.Subsystem.Commutation

/-! # Full paid boundary preparation commutes with the independent original target metadata -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary

noncomputable section

open EncodedBit LengthCoordinates NumberTheory.SharedEEA

private lemma output_outside (width : Nat) (field : Field) (output : Fin width.size) :
    ((LengthCopy.target width field).bit output).wire ∉
      Set.range (placement width field).subsystem.wires := by
  rintro ⟨selected, same⟩
  have outside : ∀ selected,
      (placement width field).subsystem.wires selected ≠
        ((LengthCopy.target width field).bit output).wire := by
    intro selected
    change (wordPairSubsystem _ _ _ _ _).wires selected ≠ _
    refine Fin.addCases (m := ScanMetadata.addressWidth width)
      (n := ScanMetadata.addressWidth width) (fun input => ?_) (fun target => ?_) selected
    · rw [wordPairSubsystem_left]
      change ((source width field).bit input).wire ≠
        (sourceBit width (outputBit width field output)).wire
      unfold source
      dsimp only
      split
      · exact (source_conjunction_ne width _).symm
      · exact source_source_ne width _ _ (boundary_output_ne width field _ output)
    · rw [wordPairSubsystem_right]
      exact (source_prefix_ne width (outputBit width field output) target).symm
  exact outside selected same

/-- The actual public load uses only real prefix X gates, independent of the original output. -/
lemma constantStep_output_comm (width : Nat) (field : Field)
    (mask : Fin (2 ^ width.size)) (state : Data width) :
    constantStep width field (Word.xorConstantStep (LengthCopy.target width field) mask state) =
      Word.xorConstantStep (LengthCopy.target width field) mask
        (constantStep width field state) := by
  apply Word.stepList_xorConstantStep_comm
  intro output gate member
  obtain ⟨input, _present, rfl⟩ := List.mem_map.mp member
  exact (source_prefix_ne width (outputBit width field output) input.rev).symm

/-- The actual native inverse adder touches the other metadata and prefix, not its output field. -/
lemma subtractStep_output_comm (width : Nat) (field : Field)
    (mask : Fin (2 ^ width.size)) (state : Data width) :
    (placement width field).subtractStep
        (Word.xorConstantStep (LengthCopy.target width field) mask state) =
      Word.xorConstantStep (LengthCopy.target width field) mask
        ((placement width field).subtractStep state) :=
  (placement width field).subsystem.full_step_xorConstantStep_comm
    Addition.TTK.WordPlacement.source_onto (encoding_surjective width)
    (LengthCopy.target width field) mask (output_outside width field)
    Addition.TTK.subtractionOutput state

/-- Complete output commutation justifies the actual adjoint cleanup after a finite length write. -/
lemma prepareStep_output_comm (width : Nat) (field : Field)
    (mask : Fin (2 ^ width.size)) (state : Data width) :
    prepareStep width field (Word.xorConstantStep (LengthCopy.target width field) mask state) =
      Word.xorConstantStep (LengthCopy.target width field) mask
        (prepareStep width field state) := by
  rw [prepareStep, constantStep_output_comm, subtractStep_output_comm]
  rfl

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthBoundary
