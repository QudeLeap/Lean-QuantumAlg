/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Primitives.WalshHadamard.Mathematics
import all QuantumAlg.Core.Measure.Instrument
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Exact phase of Hadamard followed by Z measurement

These entries use the existing literal Hadamard layer and the projector of
the existing Z measurement. Every other system remains in the arbitrary
reference factor. Thus the calculation retains relative phases and all
reference coordinates before any state or probability is observed.

The measured arithmetic word contributes its Walsh character, canceled by
the actual selected Pauli-Z gates after recomputation
[LYL+26, sec_point_add/sec_point_add.tex:67-105]. The measurement does not
release the measured register; its reset is a separate executed operation.
-/

namespace QuantumAlg.MeasuredUncompute

noncomputable section

/-- The actual Hadamard layer and Z projector retain the complete reference coordinate. -/
theorem measuredHadamard_reference_entry (width : Nat) {Reference : Register}
    (outcome row column : Fin (2 ^ width)) (leftRef rightRef : Reference.Index) :
    (ZMeasurement.projector (R := Register.prod (Qubits width) Reference)
        (fun index => index.1) outcome *
      (UnitaryOperator.prodTensor (WalshHadamard.hadamardLayerOperator width)
        (1 : UnitaryOperator Reference) : HilbertOperator
          (Register.prod (Qubits width) Reference))) (row, leftRef) (column, rightRef) =
      if row = outcome ∧ leftRef = rightRef then
        WalshHadamard.invSqrtCard width * WalshHadamard.walshSign outcome column
      else 0 := by
  rw [ZMeasurement.projector, Matrix.diagonal_mul,
    UnitaryOperator.prodTensor_apply, WalshHadamard.hadamardLayerOperator_apply]
  change (if row = outcome then (1 : ℂ) else 0) *
      ((WalshHadamard.invSqrtCard width * WalshHadamard.walshSign row column) *
        if leftRef = rightRef then 1 else 0) = _
  by_cases measured : row = outcome <;> by_cases reference : leftRef = rightRef <;>
    simp [measured, reference]

/-- The same recomputed word's correction cancels its measured character exactly. -/
theorem measuredHadamard_corrected_reference_entry (width : Nat) {Reference : Register}
    (outcome row column : Fin (2 ^ width)) (leftRef rightRef : Reference.Index) :
    WalshHadamard.walshSign outcome column *
      (ZMeasurement.projector (R := Register.prod (Qubits width) Reference)
          (fun index => index.1) outcome *
        (UnitaryOperator.prodTensor (WalshHadamard.hadamardLayerOperator width)
          (1 : UnitaryOperator Reference) : HilbertOperator
            (Register.prod (Qubits width) Reference))) (row, leftRef) (column, rightRef) =
      if row = outcome ∧ leftRef = rightRef then WalshHadamard.invSqrtCard width else 0 := by
  rw [measuredHadamard_reference_entry]
  by_cases selected : row = outcome ∧ leftRef = rightRef
  · rw [if_pos selected, if_pos selected, mul_left_comm,
      WalshHadamard.walshSign_mul_self, mul_one]
  · rw [if_neg selected, if_neg selected, mul_zero]

end

end QuantumAlg.MeasuredUncompute
