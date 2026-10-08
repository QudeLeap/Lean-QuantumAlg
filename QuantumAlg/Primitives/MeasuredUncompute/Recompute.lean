/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Character
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint

/-!
# Actual recomputation, selected Z correction, and inverse recomputation

The same native unitary computes a word and later uncomputes it. Between
these operations, the literal Z gates selected by a previously stored
measurement outcome supply the exact measured character. The resulting
full-state equation cancels that character without discarding a relative
phase or a live register [LYL+26, sec_point_add/sec_point_add.tex:85-105].

The realization premise is an internal composition interface for the
actual arithmetic program. Concrete arithmetic must establish it on the
original input domain; this lemma does not replace that program by an oracle.
-/

namespace QuantumAlg.MeasuredUncompute.Recompute

noncomputable section

open EncodedBit.Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}
variable (physical : QubitLayout encoding.width)

/-- Recompute, execute the literal selected phases, and run the same recomputation backwards. -/
def program (compute : UnitaryCircuit AlgorithmGate.model .empty physical.toQuantum)
    (word : EncodedBit.Word encoding width) (mask : Fin width → Bool) :
    UnitaryCircuit AlgorithmGate.model .empty physical.toQuantum :=
  compute.seq ((PhaseCorrection.program physical .empty word mask).seq
    (compute.dagger (AlgorithmGate.oracleFreeAdjoints .empty)))

/-- The actual inverse restores the complete original label after the selected phase. -/
theorem recompute_phase_ket
    (compute : UnitaryCircuit AlgorithmGate.model .empty physical.toQuantum)
    {step : Data → Data} (realizes : UnitaryCircuit.Realizes encoding compute step)
    (word : EncodedBit.Word encoding width) (mask : Fin width → Bool) (state : Data) :
    (program physical compute word mask).applyVec
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec =
      PhaseCorrection.sign word (step state) (PhaseCorrection.selected mask) •
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec := by
  have forward := realizes.apply_encoded_ket state
  let inverse := compute.dagger (AlgorithmGate.oracleFreeAdjoints .empty)
  have inverse_eq : inverse.matrix = compute.matrix⁻¹ := by
    change (compute.dagger (AlgorithmGate.oracleFreeAdjoints .empty)).matrix = _
    rw [UnitaryCircuit.dagger_matrix]
    exact Unitary.star_eq_inv _
  have backward : inverse.applyNormalized
      (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (encoding.encode (step state)))) =
        NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state)) :=
    (congrArg inverse.applyNormalized forward).symm.trans
      (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
        compute inverse inverse_eq _)
  have forwardVec : compute.applyVec
      (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (encoding.encode state))).vec =
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode (step state)))).vec :=
    congrArg NormalizedVector.vec forward
  have backwardVec : inverse.applyVec
      (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (encoding.encode (step state)))).vec =
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm (encoding.encode state))).vec :=
    congrArg NormalizedVector.vec backward
  rw [program, UnitaryCircuit.applyVec_seq, forwardVec, UnitaryCircuit.applyVec_seq,
    PhaseCorrection.program, PhaseCorrection.phaseCorrection_sequence_ket,
    UnitaryCircuit.applyVec_smul]
  simpa only [inverse] using congrArg
    (fun vector => PhaseCorrection.sign word (step state)
      (PhaseCorrection.selected mask) • vector) backwardVec

/-- The recomputed word cancels exactly its earlier measurement character. -/
theorem recompute_cancels_measured_ket
    (compute : UnitaryCircuit AlgorithmGate.model .empty physical.toQuantum)
    {step : Data → Data} (realizes : UnitaryCircuit.Realizes encoding compute step)
    (word : EncodedBit.Word encoding width) (state : Data) (value outcome : Fin (2 ^ width))
    (reads : ∀ index, (word.bit index).get (step state) = value.val.testBit index.val) :
    (program physical compute word (fun index => outcome.val.testBit index.val)).applyVec
        (WalshHadamard.walshSign outcome value •
          (NormalizedVector.ket (R := physical.toQuantum.register)
            (physical.basisEquiv.symm (encoding.encode state))).vec) =
      (NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm (encoding.encode state))).vec := by
  rw [UnitaryCircuit.applyVec_smul, recompute_phase_ket physical compute realizes,
    measuredCorrection_sign_walsh word (step state) value outcome reads, smul_smul,
    WalshHadamard.walshSign_mul_self, one_smul]

/-- Every external-reference column retains the same exact relative character. -/
theorem recompute_reference_entry
    (compute : UnitaryCircuit AlgorithmGate.model .empty physical.toQuantum)
    {step : Data → Data} (realizes : UnitaryCircuit.Realizes encoding compute step)
    (word : EncodedBit.Word encoding width) (mask : Fin width → Bool) (state : Data)
    {Reference : Register} (row : physical.toQuantum.register.Index)
    (left right : Reference.Index) :
    UnitaryOperator.prodTensor (program physical compute word mask).matrix
        (1 : UnitaryOperator Reference) (row, left)
        (physical.basisEquiv.symm (encoding.encode state), right) =
      if row = physical.basisEquiv.symm (encoding.encode state) ∧ left = right then
        PhaseCorrection.sign word (step state) (PhaseCorrection.selected mask) else 0 := by
  have column := congrArg
    (fun vector : HilbertVector physical.toQuantum.register => vector row)
    (recompute_phase_ket physical compute realizes word mask state)
  have matrixColumn :=
    (HilbertOperator.applyVec_ket ((program physical compute word mask).matrix :
      HilbertOperator physical.toQuantum.register)
      (physical.basisEquiv.symm (encoding.encode state)) row).symm.trans column
  rw [UnitaryOperator.prodTensor_apply, matrixColumn]
  simp only [PiLp.smul_apply, smul_eq_mul, NormalizedVector.ket_apply]
  change (PhaseCorrection.sign word (step state) (PhaseCorrection.selected mask) *
      (if row = physical.basisEquiv.symm (encoding.encode state) then 1 else 0)) *
      (if left = right then 1 else 0) = _
  by_cases selected : row = physical.basisEquiv.symm (encoding.encode state) <;>
    by_cases reference : left = right <;>
    simp [selected, reference]

end

end QuantumAlg.MeasuredUncompute.Recompute
