/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.BasisLoad
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

open EncodedBit.Word

/-- The selected reset is exactly the inverse of the literal set-bit X sequence. -/
def program {width : Nat} (outcome : Fin (2 ^ width)) : UnitaryCircuit (Qubits width) :=
  (BasisLoad.program outcome).dagger

/-- The branch's measured word becomes zero with its exact phase preserved. -/
theorem storedWordReset_ket {width : Nat} (outcome : Fin (2 ^ width)) :
    (program outcome).applyNormalized (NormalizedVector.ket (R := Qubits width) outcome) =
      NormalizedVector.ket (R := Qubits width) 0 :=
  (congrArg (BasisLoad.program outcome).dagger.applyNormalized
    (BasisLoad.basisLoad_apply_zero outcome)).symm.trans
      (UnitaryCircuit.Realizes.dagger_applyNormalized_applyNormalized (BasisLoad.program outcome) _)

/-- The same branch preserves each full reference amplitude, rather than only its marginal. -/
theorem storedWordReset_reference_entry {width : Nat} (outcome row : Fin (2 ^ width))
    {Reference : Register} (left right : Reference.Index) :
    UnitaryOperator.prodTensor (program outcome).matrix (1 : UnitaryOperator Reference)
        (row, left) (outcome, right) =
      if row = 0 ∧ left = right then 1 else 0 := by
  have column := congrArg (fun vector : NormalizedVector (Qubits width) => vector row)
    (storedWordReset_ket outcome)
  have matrixColumn :=
    (HilbertOperator.applyVec_ket ((program outcome).matrix : HilbertOperator (Qubits width))
      outcome row).symm.trans column
  rw [UnitaryOperator.prodTensor_apply, matrixColumn, NormalizedVector.ket_apply]
  change (if row = 0 then (1 : ℂ) else 0) * (if left = right then 1 else 0) = _
  by_cases zero : row = 0 <;> by_cases reference : left = right <;> simp [zero, reference]

/-- Reset retains the entire measured physical word. -/
theorem storedWordReset_physical {width : Nat} (outcome : Fin (2 ^ width)) :
    (program outcome).physical_idx = List.range width := BasisLoad.basisLoad_physicalIdx outcome

/-- Each selected X remains charged in the actual inverse sequence. -/
theorem storedWordReset_events {width : Nat} (outcome : Fin (2 ^ width)) :
    (program outcome).eventCost =
      BasisLoad.xCount outcome • ResourcePool.singleton (.gate (.builtin "x")) :=
  BasisLoad.basisLoad_eventCost outcome

/-- The branch depth is the actual number of selected X gates, including the zero branch. -/
theorem storedWordReset_depth {width : Nat} (outcome : Fin (2 ^ width)) :
    (program outcome).evaluatedEventDepth (fun _ => 1) = BasisLoad.xCount outcome :=
  BasisLoad.basisLoad_unitDepth outcome

end

end QuantumAlg.MeasuredUncompute.StoredWordReset
