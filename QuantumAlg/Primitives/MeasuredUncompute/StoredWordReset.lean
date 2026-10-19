/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.BasisLoad
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources
import all QuantumAlg.Core.Base.UnitaryCircuit.Adjoint
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Reset a measured word with the selected literal X sequence

After its Z outcome has been stored, the measured word is reset with the
inverse of the existing literal basis-loader. Its branch proof retains the
entire word and the identity on every external-reference coordinate. There
is no second measurement or deallocation in this selected unitary step
[LYL+26, sec_point_add/sec_point_add.tex:67-81]. The actual stored-result
selection and write sequence are separate circuit composition obligations.
-/

namespace QuantumAlg.MeasuredUncompute.StoredWordReset

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit.Word

/-- The selected reset is exactly the inverse of the literal set-bit X sequence. -/
def program {width : Nat} (physical : QubitLayout width)
    (outcome : Fin (2 ^ width)) :
    UnitaryCircuit AlgorithmGate.model .empty physical.toQuantum :=
  (BasisLoad.program physical .empty outcome).dagger
    (AlgorithmGate.oracleFreeAdjoints .empty)

/-- The branch's measured word becomes zero with its exact phase preserved. -/
lemma storedWordReset_ket {width : Nat} (physical : QubitLayout width)
    (outcome : Fin (2 ^ width)) :
    ((program physical outcome).applyNormalized environment)
        (NormalizedVector.ket (R := physical.toQuantum.register)
          (physical.basisEquiv.symm outcome)) =
      NormalizedVector.ket (R := physical.toQuantum.register)
        (physical.basisEquiv.symm 0) := by
  have inverseEq : ((program physical outcome).matrix environment) =
      ((BasisLoad.program physical .empty outcome).matrix environment)⁻¹ := by
    rw [program, UnitaryCircuit.dagger_matrix]
    rw [Subsingleton.elim
      ((AlgorithmGate.oracleFreeAdjoints .empty).interpretation environment) environment]
    exact Unitary.star_eq_inv _
  have forward := BasisLoad.basisLoad_apply_zero (environment := environment) physical .empty
    outcome
  rw [← forward]
  exact UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized
    (BasisLoad.program physical .empty outcome) (program physical outcome) inverseEq _

/-- The same branch preserves each full reference amplitude, rather than only its marginal. -/
lemma storedWordReset_reference_entry {width : Nat} (physical : QubitLayout width)
    (outcome : Fin (2 ^ width))
    (row : physical.toQuantum.register.Index)
    {Reference : Register} (left right : Reference.Index) :
    UnitaryOperator.prodTensor ((program physical outcome).matrix environment)
        (1 : UnitaryOperator Reference)
        (row, left) (physical.basisEquiv.symm outcome, right) =
      if row = physical.basisEquiv.symm 0 ∧ left = right then 1 else 0 := by
  have column := congrArg
    (fun vector : NormalizedVector physical.toQuantum.register => vector row)
    (storedWordReset_ket (environment := environment) physical outcome)
  have matrixColumn :=
    (HilbertOperator.applyVec_ket
      (((program physical outcome).matrix environment) : HilbertOperator
        physical.toQuantum.register)
      (physical.basisEquiv.symm outcome) row).symm.trans column
  rw [UnitaryOperator.prodTensor_apply, matrixColumn, NormalizedVector.ket_apply]
  change (if row = physical.basisEquiv.symm 0 then (1 : ℂ) else 0) *
      (if left = right then 1 else 0) = _
  by_cases zero : row = physical.basisEquiv.symm 0 <;>
    by_cases reference : left = right <;> simp [zero, reference]

/-- Canonical binary coordinates of the same executed native inverse sequence. -/
def binaryProgram (environment : OracleModel.empty.Interpretation) {width : Nat} (outcome : Fin (2 ^
  width)) :
    UnitaryOperator (Qubits width) :=
  ((program (QubitLayout.canonical width) outcome).binaryMatrix environment)

/-- The binary-coordinate reset sends the observed word to zero with exact phase. -/
lemma storedWordReset_binary_ket {width : Nat} (outcome : Fin (2 ^ width)) :
    (binaryProgram environment outcome).apply (NormalizedVector.ket (R := Qubits width) outcome) =
      NormalizedVector.ket (R := Qubits width) 0 :=
  UnitaryCircuit.Realizes.binaryMatrix_apply_ket_eq_of_applyNormalized_encoded_ket
    (program (QubitLayout.canonical width) outcome) outcome 0
    (storedWordReset_ket (QubitLayout.canonical width) outcome)

/-- The canonical view preserves each external-reference matrix entry. -/
lemma storedWordReset_binary_reference_entry {width : Nat}
    (outcome row : Fin (2 ^ width)) {Reference : Register}
    (left right : Reference.Index) :
    UnitaryOperator.prodTensor (binaryProgram environment outcome) (1 : UnitaryOperator Reference)
        (row, left) (outcome, right) =
      if row = 0 ∧ left = right then 1 else 0 := by
  have column := congrArg (fun vector : NormalizedVector (Qubits width) => vector row)
    (storedWordReset_binary_ket (environment := environment) outcome)
  have matrixColumn :=
    (HilbertOperator.applyVec_ket (binaryProgram environment outcome : HilbertOperator (Qubits
      width))
      outcome row).symm.trans column
  rw [UnitaryOperator.prodTensor_apply, matrixColumn, NormalizedVector.ket_apply]
  change (if row = 0 then (1 : ℂ) else 0) * (if left = right then 1 else 0) = _
  by_cases zero : row = 0 <;> by_cases reference : left = right <;> simp [zero, reference]

/-- Each selected X remains charged in the actual inverse sequence. -/
lemma storedWordReset_events {width : Nat} (physical : QubitLayout width)
    (outcome : Fin (2 ^ width)) :
    (program physical outcome).eventCost =
      BasisLoad.xCount outcome •
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty)
          (.gate .singleQubit) := by
  rw [program, AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost,
    BasisLoad.basisLoad_eventCost]
  change Multiset.map (AlgorithmGate.oracleFreeEvent .empty)
      (BasisLoad.xCount outcome • Multiset.replicate 1 (.gate .singleQubit)) =
    BasisLoad.xCount outcome • Multiset.replicate 1 (.gate .singleQubit)
  simp [Multiset.map_nsmul, AlgorithmGate.oracleFreeEvent]

/-- The branch depth is the actual number of selected X gates, including the zero branch. -/
lemma storedWordReset_depth {width : Nat} (physical : QubitLayout width)
    (outcome : Fin (2 ^ width)) :
    (program physical outcome).evaluatedEventDepth (fun _ => 1) =
      BasisLoad.xCount outcome := by
  rw [program, AlgorithmGate.algorithmGate_oracleFreeAdjoints_unit_depth]
  exact BasisLoad.basisLoad_unitDepth physical .empty outcome

end

end QuantumAlg.MeasuredUncompute.StoredWordReset
