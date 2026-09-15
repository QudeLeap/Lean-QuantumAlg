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

/-! # Physical footprint of the VBE modular-adder circuit -/

section

namespace QuantumAlg.MAU.Addition.VBECircuit

noncomputable section

/-- The clean-carry/sum core stays inside its canonical plain-adder carrier. -/
theorem activeAdderCoreProgram_physical_idx_subset_range (n : Nat) :
    (activeAdderCoreProgram n).physical_idx ⊆
      List.range
        (PlainAdder.Schedule.PowerOfTwo.dataWithCarryWorkEncoding
          (AdderWidth n)).width := by
  exact
    PlainAdder.Schedule.PowerOfTwo.carryWorkCleanCarrySumProgram_physical_idx_subset_range
      (AdderWidth n)

/-- The forward plain-adder core remains in range after parking the source and
appending the reduction flag. -/
theorem activeAdderCarrierProgram_physical_idx_subset_range (n : Nat) :
    (activeAdderCarrierProgram n).physical_idx ⊆ List.range (rawEncoding n).width := by
  unfold activeAdderCarrierProgram
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  apply UnitaryCircuit.insertMiddle_physical_idx_subset_range
  exact activeAdderCoreProgram_physical_idx_subset_range n

/-- The forward VBE plain-adder stage stays in the VBE carrier. -/
theorem activeAdderProgram_physical_idx_subset_range (n : Nat) :
    (activeAdderProgram n).physical_idx ⊆ List.range (encoding n).width := by
  exact activeAdderCarrierProgram_physical_idx_subset_range n

/-- The reversed clean-carry/sum core stays inside its canonical plain-adder
carrier. -/
theorem adderInverseCoreProgram_physical_idx_subset_range (n : Nat) :
    (adderInverseCoreProgram n).physical_idx ⊆
      List.range
        (PlainAdder.Schedule.PowerOfTwo.dataWithCarryWorkEncoding
          (AdderWidth n)).width := by
  unfold adderInverseCoreProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The reversed plain-adder core remains in range after parking the source
and appending the reduction flag. -/
theorem activeAdderInverseCarrierProgram_physical_idx_subset_range (n : Nat) :
    (activeAdderInverseCarrierProgram n).physical_idx ⊆
      List.range (rawEncoding n).width := by
  unfold activeAdderInverseCarrierProgram
  apply UnitaryCircuit.prodLeft_physical_idx_subset_range
  apply UnitaryCircuit.insertMiddle_physical_idx_subset_range
  exact adderInverseCoreProgram_physical_idx_subset_range n

/-- The reversed VBE plain-adder stage stays in the VBE carrier. -/
theorem activeAdderInverseProgram_physical_idx_subset_range (n : Nat) :
    (activeAdderInverseProgram n).physical_idx ⊆ List.range (encoding n).width := by
  exact activeAdderInverseCarrierProgram_physical_idx_subset_range n

/-- The VBE source-routing word swap stays in its common carrier. -/
theorem sourceSwapProgram_physical_idx_subset_range (n : Nat) :
    (sourceSwapProgram n).physical_idx ⊆ List.range (encoding n).width := by
  unfold sourceSwapProgram
  exact EncodedBit.Word.swapProgram_physical_idx_subset_range
    (activeSourceLowWord n) (parkedSourceWord n)
    (activeSourceLow_parked_diagonal_ne n)

/-- The two-gate reduction-flag copy stays in the VBE carrier. -/
theorem copyReductionFlagProgram_physical_idx_subset_range (n : Nat) :
    (copyReductionFlagProgram n).physical_idx ⊆ List.range (encoding n).width := by
  unfold copyReductionFlagProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The final reduction-flag cleanup CNOT stays in the VBE carrier. -/
theorem cleanupReductionFlagProgram_physical_idx_subset_range (n : Nat) :
    (cleanupReductionFlagProgram n).physical_idx ⊆ List.range (encoding n).width := by
  unfold cleanupReductionFlagProgram
  exact EncodedBit.GateSpec.program_physical_idx_subset_range _

/-- The controlled modulus clear stays in the VBE carrier. -/
theorem clearActiveModulusProgram_physical_idx_subset_range (n N : Nat) :
    (clearActiveModulusProgram n N).physical_idx ⊆
      List.range (encoding n).width := by
  unfold clearActiveModulusProgram
  exact EncodedBit.Word.controlledXorConstantProgram_physical_idx_subset_range
    (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
    (reductionFlag_activeSource_ne n)

/-- The reverse controlled modulus load stays in the VBE carrier. -/
theorem restoreActiveModulusProgram_physical_idx_subset_range (n N : Nat) :
    (restoreActiveModulusProgram n N).physical_idx ⊆
      List.range (encoding n).width := by
  unfold restoreActiveModulusProgram
  exact
    EncodedBit.Word.controlledXorConstantUnloadProgram_physical_idx_subset_range
      (reductionFlagBit n) (activeSourceWord n) (modulusWordLabel n N)
      (reductionFlag_activeSource_ne n)

/-- Every stage of the concrete VBE compare/subtract/add-back schedule stays
inside its common carrier. -/
theorem modularAddProgram_physical_idx_subset_range (n N : Nat) :
    (modularAddProgram n N).physical_idx ⊆ List.range (encoding n).width := by
  unfold modularAddProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

end

end QuantumAlg.MAU.Addition.VBECircuit

end
