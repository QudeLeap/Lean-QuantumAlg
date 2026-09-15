/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.SwapTest.Basic
import all QuantumAlg.Components.Encoded.BitGates.RegisterSwap.Semantics
import all QuantumAlg.Components.Encoded.BitGates.RegisterSwap.Resources
import all QuantumAlg.Primitives.HadamardTest.Basic
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# The SWAP test built from actual Hadamard and Toffoli occurrences

The controlled exchange uses three literal Toffolis per original word position.
It acts between the two actual control Hadamards, with no auxiliary quantum
word [BCWdW01, main.tex:287-328].
-/

namespace QuantumAlg.SwapTest

noncomputable section

/-- Actual elementary gate sequence for the original SWAP-test operator. -/
def sourceCircuit (width : Nat) : UnitaryCircuit (Qubits (1 + (width + width))) :=
  (((hadamardTestHadamardLayer (width + width)).seq
    (EncodedRegisterSwap.program width)).seq
      (hadamardTestHadamardLayer (width + width))).seq
        (UnitaryCircuit.identity (Qubits (1 + (width + width)))
          (List.range (1 + (width + width))) List.nodup_range)

theorem sourceCircuit_matrix (width : Nat) :
    (sourceCircuit width).matrix = swapTest width := by
  change 1 * ((hadamardTestHadamardOp (width + width)) *
    ((EncodedRegisterSwap.program width).matrix * hadamardTestHadamardOp (width + width))) = _
  rw [one_mul, EncodedRegisterSwap.program_matrix]
  rfl

/-- Physical normalization keeps the actual complete register and adds no operation. -/
theorem sourceCircuit_physicalIdx (width : Nat) :
    (sourceCircuit width).physical_idx = List.range (1 + (width + width)) := by
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  have boundary : (hadamardTestHadamardLayer (width + width)).physical_idx ⊆
      List.range (1 + (width + width)) := by
    intro wire present
    change wire ∈ [0] at present
    obtain rfl := List.mem_singleton.mp present
    simp
  exact UnitaryCircuit.seq_physical_idx_subset _ _
    (UnitaryCircuit.seq_physical_idx_subset _ _ boundary
      (EncodedRegisterSwap.program_physical_idx_subset width)) boundary

/-- The ordered native list contains both boundary Hadamards and every elementary Toffoli. -/
theorem sourceCircuit_eventTrace (width : Nat) :
    (sourceCircuit width).eventTrace =
      [.gate (.builtin "hadamard")] ++
        List.replicate (3 * width) (.gate (.builtin "toffoli")) ++
          [.gate (.builtin "hadamard")] := by
  simp only [sourceCircuit, UnitaryCircuit.seq_eventTrace, UnitaryCircuit.identity_eventTrace,
    hadamardTestHadamardLayer_eventTrace, EncodedRegisterSwap.program_eventTrace,
    List.append_nil]
  rfl

end

end QuantumAlg.SwapTest
