/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Layout
import all QuantumAlg.Algorithms.OrderFinding.BornModel

/-!
# The unchanged inverse-QFT amplitudes on the complete Shor bank

The original inverse-QFT layer acts only on the phase positions. The two
remaining words are the actual power and arithmetic auxiliary; their exact
matrix factor is identity. Thus the source phase amplitudes are retained
without dropping the unmeasured systems [Sho95, source.tex:1206-1245].
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum

noncomputable section

/-- The actual inverse-QFT readout leaves the complete two-word target label unchanged. -/
theorem readout_basis_entry (N : Nat) (phase exponent : Fin (2 ^ phaseBits N))
    (target source : Fin (2 ^ (modulusBits N + modulusBits N))) :
    (OrderFinding.orderFindingReadoutCircuit (phaseBits N)
      (modulusBits N + modulusBits N)).applyVec
        (NormalizedVector.ket (R := Qubits (totalQubits N)) (prodEquiv (exponent, source))).vec
          (prodEquiv (phase, target)) =
      star (invSqrtN (phaseBits N) * ω (phaseBits N) ^ (exponent.val * phase.val)) *
        if target = source then 1 else 0 := by
  have column := HilbertOperator.applyVec_ket
    (R := Qubits (phaseBits N + (modulusBits N + modulusBits N)))
    ((OrderFinding.orderFindingReadoutCircuit (phaseBits N)
      (modulusBits N + modulusBits N)).matrix :
      HilbertOperator (Qubits (phaseBits N + (modulusBits N + modulusBits N))))
    (prodEquiv (exponent, source)) (prodEquiv (phase, target))
  refine column.trans ?_
  simp only [OrderFinding.orderFindingReadoutCircuit, UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_apply, Equiv.symm_apply_apply,
    UnitaryCircuit.dagger_matrix, QFTCircuit_matrix,
    Matrix.conjTranspose_apply, QFTOperator_entry, OrderFinding.BornBridge.identityCircuit_entry]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum
