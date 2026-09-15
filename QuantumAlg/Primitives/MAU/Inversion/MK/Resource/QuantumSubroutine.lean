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
import all QuantumAlg.Primitives.MAU.Inversion.MK.Physical.Resource

/-! # Quantum-subroutine absence for the actual unscaled inversion circuit -/

section

namespace QuantumAlg.MAU.Inversion.MK.Resource

noncomputable section

/-- The exact seven-stage Montgomery--Kaliski inversion circuit has no opaque
quantum-subroutine event: every stage is a concrete encoded-bit circuit or a
structural lift of one. -/
theorem unscaledInversionProgram_quantumSubroutine_count_zero
    (tail counterWidth p : Nat)
    (comparisonIndex : Fin tail.succ)
    (workIndex : Fin (counterWidth - 1))
    (hpOdd : Odd p)
    (label : QuantumAlg.Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
      (unscaledInversionProgram
        tail counterWidth p comparisonIndex workIndex hpOdd).eventCost = 0 := by
  unfold unscaledInversionProgram
  exact EncodedBit.GateSpec.programList_quantumSubroutine_count_zero _ label

end

end QuantumAlg.MAU.Inversion.MK.Resource

end
