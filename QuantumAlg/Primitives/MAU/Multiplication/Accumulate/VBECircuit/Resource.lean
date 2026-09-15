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

/-! # Structural resource certificate for the lifted VBE modular adder -/

section

namespace QuantumAlg
namespace MAU.Multiplication.Accumulate
namespace VBECircuit

noncomputable section

/-- Lifting the VBE modular adder past its multiplier word preserves its
absence of quantum-subroutine events. -/
theorem liftedModularAddProgram_quantumSubroutine_count_zero
    (n N : Nat) (label : QuantumAlg.Resource.QuantumSubroutineLabel) :
    ResourcePool.count (.quantumSubroutine label)
      (liftedModularAddProgram n N).eventCost = 0 := by
  unfold liftedModularAddProgram
  change ResourcePool.count (.quantumSubroutine label)
    (UnitaryCircuit.prodRight
      (m := (PlainAdder.Schedule.PowerOfTwo.wordEncoding n).width)
      (MAU.Addition.VBECircuit.modularAddProgram n N)).eventCost = 0
  rw [UnitaryCircuit.prodRight_eventCost]
  exact MAU.Addition.VBECircuit.modularAddProgram_quantumSubroutine_count_zero
    n N label

end

end VBECircuit
end MAU.Multiplication.Accumulate
end QuantumAlg

end
