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

/-! # Physical footprint of the lifted VBE modular-adder stage -/

section

namespace QuantumAlg.MAU.Multiplication.Accumulate.VBECircuit

noncomputable section

/-- The arithmetic VBE modular-adder remains in range after lifting it past
the unchanged multiplier word. -/
theorem liftedModularAddProgram_physical_idx_subset_range (n N : Nat) :
    (liftedModularAddProgram n N).physical_idx ⊆
      List.range (encoding n).width := by
  unfold liftedModularAddProgram
  apply UnitaryCircuit.prodRight_physical_idx_subset_range
  exact MAU.Addition.VBECircuit.modularAddProgram_physical_idx_subset_range n N

end

end QuantumAlg.MAU.Multiplication.Accumulate.VBECircuit

end
