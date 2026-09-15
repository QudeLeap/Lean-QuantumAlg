/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.Layout
import all QuantumAlg.Primitives.MAU.Multiplication.VBECircuit
import QuantumAlg.Init
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Primitives.MAU.Inversion.MK.Circuit.Resource
import all QuantumAlg.Primitives.MAU.Inversion.MK.StructuredWitness
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Physical
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.VBECircuit.Resource
import all QuantumAlg.Primitives.MAU.Inversion.MK.Correction
import all QuantumAlg.Primitives.MAU.Inversion.MK.Correction.Resource

/-! # Physical footprint of the inversion correction stages -/

section

namespace QuantumAlg.MAU.Inversion.MK.Correction

noncomputable section

/-- Lifting a fixed-round program over the VBE workspace and public target
preserves a canonical physical-range certificate. -/
theorem liftFixedProgram_physical_idx_subset_range
    (tail counterWidth : Nat)
    (program : UnitaryCircuit (Qubits
      (MK.Circuit.encoding tail.succ counterWidth).width))
    (contained : program.physical_idx ⊆
      List.range (MK.Circuit.encoding tail.succ counterWidth).width) :
    (liftFixedProgram tail counterWidth program).physical_idx ⊆
      List.range (encoding tail counterWidth).width := by
  unfold liftFixedProgram
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  exact contained

/-- The fixed-round compute payload remains inside the correction carrier. -/
theorem fixedComputeProgram_physical_idx_subset_range
    (tail counterWidth : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1)) :
    (fixedComputeProgram tail counterWidth comparisonIndex workIndex).physical_idx ⊆
      List.range (encoding tail counterWidth).width := by
  unfold fixedComputeProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- Lifting a VBE-workspace program over fixed-round state and public target
preserves a canonical physical-range certificate. -/
theorem liftWorkProgram_physical_idx_subset_range
    (tail counterWidth : Nat)
    (program : UnitaryCircuit (Qubits
      (MAU.Multiplication.VBECircuit.encoding tail.succ).width))
    (contained : program.physical_idx ⊆
      List.range (MAU.Multiplication.VBECircuit.encoding tail.succ).width) :
    (liftWorkProgram tail counterWidth program).physical_idx ⊆
      List.range (encoding tail counterWidth).width := by
  unfold liftWorkProgram
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  apply UnitaryCircuit.prodRight_physical_idx_subset_range
  exact contained

/-- The complete unit-multiplication payload stays in range after it is lifted
into the inversion correction carrier. -/
theorem liftedUnitMultiplicationProgram_physical_idx_subset_range
    (tail counterWidth p : Nat) (unit : (ZMod p)ˣ) :
    (liftedUnitMultiplicationProgram tail counterWidth p unit).physical_idx ⊆
      List.range (encoding tail counterWidth).width := by
  unfold liftedUnitMultiplicationProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- One direct counter-selected multiplication payload stays in the correction
carrier. -/
theorem counterCorrectionBitProgram_physical_idx_subset_range
    (tail counterWidth p : Nat) (hpOdd : Odd p) (bit : Fin counterWidth) :
    (counterCorrectionBitProgram tail counterWidth p hpOdd bit).physical_idx ⊆
      List.range (encoding tail counterWidth).width := by
  unfold counterCorrectionBitProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The fold of all counter-selected multiplication payloads stays in the
correction carrier. -/
theorem counterCorrectionProgram_physical_idx_subset_range
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    (counterCorrectionProgram tail counterWidth p hpOdd).physical_idx ⊆
      List.range (encoding tail counterWidth).width := by
  unfold counterCorrectionProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The static sign-correction multiplication stays in the correction carrier. -/
theorem signCorrectionProgram_physical_idx_subset_range
    (tail counterWidth p : Nat) :
    (signCorrectionProgram tail counterWidth p).physical_idx ⊆
      List.range (encoding tail counterWidth).width := by
  unfold signCorrectionProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The load, reduction, copy, and reverse-uncompute stages for the raw
pseudo-residue remain in the correction carrier. -/
theorem rawPseudoResidueLoadProgram_physical_idx_subset_range
    (tail counterWidth p : Nat) :
    (rawPseudoResidueLoadProgram tail counterWidth p).physical_idx ⊆
      List.range (encoding tail counterWidth).width := by
  unfold rawPseudoResidueLoadProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The raw load, counter correction, and sign correction together stay in
the common correction carrier. -/
theorem correctionComputeProgram_physical_idx_subset_range
    (tail counterWidth p : Nat) (hpOdd : Odd p) :
    (correctionComputeProgram tail counterWidth p hpOdd).physical_idx ⊆
      List.range (encoding tail counterWidth).width := by
  unfold correctionComputeProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The staged public-target transfer, VBE add, and reverse transfers remain
inside the common correction carrier. -/
theorem stagedTargetAddProgram_physical_idx_subset_range
    (tail counterWidth p : Nat) :
    (stagedTargetAddProgram tail counterWidth p).physical_idx ⊆
      List.range (encoding tail counterWidth).width := by
  unfold stagedTargetAddProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

end

end QuantumAlg.MAU.Inversion.MK.Correction

end
