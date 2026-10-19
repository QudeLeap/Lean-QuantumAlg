/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.MeasurementPhase
import all QuantumAlg.Core.Base.Gate.Basic

/-!
# Measured arithmetic words in coherent superposition

Linearity of the actual Hadamard-and-Z operator retains the phase of every
input amplitude, including words entangled with the unmeasured register.
The reference label may contain all remaining arithmetic systems together
with an external reference. No normalization or separability premise is
required for this unnormalized branch equation.

The word-dependent phase is the one removed after arithmetic recomputation
[LYL+26, sec_point_add/sec_point_add.tex:67-105]. The measured register still
contains its outcome; its subsequent reset remains part of the real circuit.
-/

namespace QuantumAlg.MeasuredUncompute

noncomputable section

/-- Mathematical operator of the existing Hadamard layer followed by one existing Z branch. -/
def measuredOperator (width : Nat) (Reference : Register) (outcome : Fin (2 ^ width)) :
    HilbertOperator (Register.prod (Qubits width) Reference) :=
  ZMeasurement.projector (R := Register.prod (Qubits width) Reference)
      (fun index => index.1) outcome *
    (UnitaryOperator.prodTensor (WalshHadamard.hadamardLayerOperator width)
      (1 : UnitaryOperator Reference) : HilbertOperator (Register.prod (Qubits width) Reference))

/-- Every reference-labelled input ket retains its own exact measured character. -/
lemma measuredHadamard_reference_ket (width : Nat) {Reference : Register}
    (outcome value : Fin (2 ^ width)) (reference : Reference.Index) :
    (measuredOperator width Reference outcome).applyVec
        (NormalizedVector.ket (R := Register.prod (Qubits width) Reference)
          (value, reference)).vec =
      (WalshHadamard.invSqrtCard width * WalshHadamard.walshSign outcome value) •
        (NormalizedVector.ket (R := Register.prod (Qubits width) Reference)
          (outcome, reference)).vec := by
  ext index
  rcases index with ⟨row, other⟩
  rw [HilbertOperator.applyVec_ket]
  rw [measuredOperator, measuredHadamard_reference_entry]
  by_cases measured : row = outcome ∧ other = reference
  · obtain ⟨rfl, rfl⟩ := measured
    simp [NormalizedVector.ket_apply]
  · have different : ((row, other) : (Register.prod (Qubits width) Reference).Index) ≠
        (outcome, reference) := by
      intro same
      exact measured ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩
    simp [NormalizedVector.ket_apply, measured, different]

/-- The same physical branch preserves the characters of arbitrary coherent, entangled inputs. -/
lemma measuredHadamard_coherent_reference (width : Nat) {Reference : Register}
    (outcome : Fin (2 ^ width)) (value : Reference.Index → Fin (2 ^ width))
    (amplitude : Reference.Index → ℂ) :
    (measuredOperator width Reference outcome).applyVec
        (∑ reference : Reference.Index, amplitude reference •
          (NormalizedVector.ket (R := Register.prod (Qubits width) Reference)
            (value reference, reference)).vec) =
      ∑ reference : Reference.Index,
        (amplitude reference *
          (WalshHadamard.invSqrtCard width * WalshHadamard.walshSign outcome (value reference))) •
          (NormalizedVector.ket (R := Register.prod (Qubits width) Reference)
            (outcome, reference)).vec := by
  rw [HilbertOperator.applyVec_sum]
  apply Finset.sum_congr rfl
  intro reference _
  rw [HilbertOperator.applyVec_smul, measuredHadamard_reference_ket, smul_smul]

end

end QuantumAlg.MeasuredUncompute
