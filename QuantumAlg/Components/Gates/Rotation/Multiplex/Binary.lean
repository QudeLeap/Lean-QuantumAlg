/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Rotation.Multiplex.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Components.Control
import all QuantumAlg.Util.FinPow.BinaryBasis.Append

/-!
# Binary tensor branches of the native rotation selector

The original selector and phase wire precede the complete untouched source
suffix. This is only a matrix projection of the placed four-gate circuit.
-/

namespace QuantumAlg.Gate.Rotation.Multiplex
noncomputable section

private lemma firstDecoded (width : Nat) (selector phase : Fin 2)
    (rest : Fin (2 ^ width)) :
    (QuantumSignature.qubitsIndexEquiv (1 + (1 + width))).symm
      (prodEquiv (selector, prodEquiv (phase, rest))) (0 : Fin (1 + (1 + width))) =
      selector := by
  have original := BinaryBasis.bigEndianEquiv_prod_left
    (leftWidth := 1) (rightWidth := 1 + width) selector (prodEquiv (phase, rest)) 0
  have first : (BinaryBasis.bigEndianEquiv 1).symm selector 0 = selector := by
    fin_cases selector <;> rfl
  exact original.trans first

private lemma secondDecoded (width : Nat) (selector phase : Fin 2)
    (rest : Fin (2 ^ width)) :
    (QuantumSignature.qubitsIndexEquiv (1 + (1 + width))).symm
      (prodEquiv (selector, prodEquiv (phase, rest)))
      (Fin.natAdd 1 (0 : Fin (1 + width))) = phase := by
  have suffix := BinaryBasis.bigEndianEquiv_prod_right
    (leftWidth := 1) (rightWidth := 1 + width) selector (prodEquiv (phase, rest)) 0
  have first := BinaryBasis.bigEndianEquiv_prod_left
    (leftWidth := 1) (rightWidth := width) phase rest 0
  have phaseValue : (BinaryBasis.bigEndianEquiv 1).symm phase 0 = phase := by
    fin_cases phase <;> rfl
  exact suffix.trans (first.trans phaseValue)

private def binaryWeight (width : Nat) (zeroAngle oneAngle : ℝ)
    (label : Fin (2 ^ (1 + (1 + width)))) : ℂ :=
  let control : Fin 2 := (QuantumSignature.qubitsIndexEquiv (1 + (1 + width))).symm label
    (0 : Fin (1 + (1 + width)))
  let phase : Fin 2 := (QuantumSignature.qubitsIndexEquiv (1 + (1 + width))).symm label
    (Fin.natAdd 1 (0 : Fin (1 + width)))
  weight (if control = 0 then zeroAngle else oneAngle) phase

private lemma binaryWeight_triple (width : Nat) (zeroAngle oneAngle : ℝ)
    (selector phase : Fin 2) (source : Fin (2 ^ width)) :
    binaryWeight width zeroAngle oneAngle (prodEquiv (selector, prodEquiv (phase, source))) =
      weight (if selector = 0 then zeroAngle else oneAngle) phase :=
  congrArg₂ (fun control target : Fin 2 =>
    weight (if control = 0 then zeroAngle else oneAngle) target)
    (firstDecoded width selector phase source) (secondDecoded width selector phase source)

/-- Exact selector block decomposition of the placed word on the whole original source suffix. -/
lemma circuitAt_prefix_binaryMatrix (oracles : OracleModel) (width : Nat)
    (zeroAngle oneAngle : ℝ) (environment : oracles.Interpretation) :
    (((circuitAt (width := 1 + (1 + width)) 0 (Fin.natAdd 1 (0 : Fin (1 + width))) (by
      intro same
      have values := congrArg Fin.val same
      change 0 = 1 + 0 at values
      omega)
      oracles zeroAngle oneAngle).binaryMatrix environment) :
        HilbertOperator (Qubits (1 + (1 + width)))) =
      HilbertOperator.tensor HilbertOperator.proj0
        (HilbertOperator.tensor (rotZStdOp zeroAngle : HilbertOperator (Qubits 1))
          (1 : HilbertOperator (Qubits width))) +
      HilbertOperator.tensor HilbertOperator.proj1
        (HilbertOperator.tensor (rotZStdOp oneAngle : HilbertOperator (Qubits 1))
          (1 : HilbertOperator (Qubits width))) := by
  have diagonal :
      (((circuitAt (width := 1 + (1 + width)) 0 (Fin.natAdd 1 (0 : Fin (1 + width))) (by
        intro same
        have values := congrArg Fin.val same
        change 0 = 1 + 0 at values
        omega) oracles zeroAngle oneAngle).binaryMatrix environment) :
          HilbertOperator (Qubits (1 + (1 + width)))) =
        Matrix.diagonal (binaryWeight width zeroAngle oneAngle) := by
    rw [UnitaryCircuit.binaryMatrix, UnitaryOperator.coe_reindex, circuitAt_matrix]
    exact Matrix.submatrix_diagonal
      (fun basis : (QuantumSignature.qubits (1 + (1 + width))).canonicalPlacement.layout.Basis =>
        let control : Fin 2 := basis (0 : Fin (1 + (1 + width)))
        let phase : Fin 2 := basis (Fin.natAdd 1 (0 : Fin (1 + width)))
        weight (if control = 0 then zeroAngle else oneAngle) phase)
      (QuantumSignature.qubitsIndexEquiv (1 + (1 + width))).symm
      (QuantumSignature.qubitsIndexEquiv (1 + (1 + width))).symm.injective
  rw [diagonal]
  ext row column
  obtain ⟨⟨rowSelector, rowRest⟩, rfl⟩ :=
    (prodEquiv (m := 1) (n := 1 + width)).surjective row
  obtain ⟨⟨rowPhase, rowSource⟩, rfl⟩ :=
    (prodEquiv (m := 1) (n := width)).surjective rowRest
  obtain ⟨⟨selector, rest⟩, rfl⟩ :=
    (prodEquiv (m := 1) (n := 1 + width)).surjective column
  obtain ⟨⟨phase, source⟩, rfl⟩ :=
    (prodEquiv (m := 1) (n := width)).surjective rest
  simp only [Matrix.diagonal_apply, Equiv.apply_eq_iff_eq, binaryWeight_triple,
    HilbertOperator.tensor_apply, Equiv.symm_apply_apply, Matrix.add_apply]
  fin_cases rowSelector <;> fin_cases selector <;> fin_cases rowPhase <;> fin_cases phase <;>
    by_cases same : rowSource = source <;>
    simp [HilbertOperator.proj0, HilbertOperator.proj1, rotZStdOp, rotZOp, weight,
      same, Matrix.one_apply]

end
end QuantumAlg.Gate.Rotation.Multiplex
