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
import all QuantumAlg.Primitives.MAU.Inversion.MK.Physical.Correction
import all QuantumAlg.Primitives.MAU.Inversion.MK.Resource

/-! # Physical footprint of the complete Montgomery--Kaliski inversion resource -/

section

namespace QuantumAlg.MAU.Inversion.MK.Resource

noncomputable section

/-- The complete fixed compute/correct/add/uncompute inversion ledger remains
inside the correction carrier. -/
theorem inversionProgram_physical_idx_subset_range
    (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    (inversionProgram tail counterWidth p comparisonIndex workIndex hpOdd).physical_idx ⊆
      List.range (Correction.encoding tail counterWidth).width := by
  unfold inversionProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

/-- The named complete Montgomery--Kaliski circuit has the footprint of its
five-stage inversion ledger. -/
theorem inversionCircuit_physical_idx_subset_range
    (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    (inversionCircuit tail counterWidth p comparisonIndex workIndex hpOdd).physical_idx ⊆
      List.range (Correction.encoding tail counterWidth).width := by
  unfold inversionCircuit
  exact inversionProgram_physical_idx_subset_range
    tail counterWidth p comparisonIndex workIndex hpOdd

/-- The complete scale-removing inversion ledger, including its two lifted
unit multiplications, remains inside the correction carrier. -/
theorem unscaledInversionProgram_physical_idx_subset_range
    (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p) :
    (unscaledInversionProgram tail counterWidth p comparisonIndex workIndex
      hpOdd).physical_idx ⊆
      List.range (Correction.encoding tail counterWidth).width := by
  unfold unscaledInversionProgram
  exact EncodedBit.GateSpec.programList_physical_idx_subset_range _

end

end QuantumAlg.MAU.Inversion.MK.Resource

end
