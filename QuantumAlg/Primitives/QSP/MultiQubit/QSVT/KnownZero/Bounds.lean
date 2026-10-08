/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.KnownZero.Block
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.MultiControl

/-!
# Uniform linear depth of expanded matching-parity execution

The bounds include the source query, both restored native masks and
conjunctions, and every phase rotation. The two Hadamard boundary gates
remain visible, including for an empty source word.
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
noncomputable section

private theorem conjunction_bound (m n : Nat) (positive : 0 < n) :
    EncodedBit.Word.OneDirtyLayout.gateCount m ≤ 8 * m + 1 := by
  have actual := (ZeroProjector.SourceWork.layout m n positive).gates_length_le
  rw [EncodedBit.Word.OneDirtyLayout.gates_length] at actual
  exact actual

/-- Actual word depth grows linearly in the phase count and original block-ancilla width. -/
theorem circuit_depth_le {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
    (positive : 0 < n) (allowControlled : Bool) (phases : List ℝ) :
    (circuit U positive allowControlled phases).evaluatedEventDepth (fun _ => 1) ≤
      (20 * m + 4) * phases.length := by
  rw [circuit_depth]
  apply Nat.mul_le_mul_right
  have bound := conjunction_bound m n positive
  omega

/-- Both boundary Hadamards remain charged in the standard zero-block implementation. -/
theorem zeroBlockCircuit_depth_le {m n : Nat} (U : UnitaryOperator (Qubits (m + n)))
    (positive : 0 < n) (allowControlled : Bool) (phases : List ℝ) :
    (zeroBlockCircuit U positive allowControlled phases).evaluatedEventDepth (fun _ => 1) ≤
      (20 * m + 4) * phases.length + 2 := by
  rw [zeroBlockCircuit_depth]
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_right
  have bound := conjunction_bound m n positive
  omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.KnownZero
