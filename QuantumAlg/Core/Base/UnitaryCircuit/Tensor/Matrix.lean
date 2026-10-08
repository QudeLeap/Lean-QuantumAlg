/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Tensor
public import QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.UnitaryCircuit.Tensor
import all QuantumAlg.Core.Base.Layout.Quantum.Append.Embedding.Entries
import all QuantumAlg.Core.Base.Layout.Quantum.Append
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Control.Operator

/-!
# Exact tensor matrix of disjoint native execution

The operator of the generated parallel word is the tensor of the two original
operators in the appended physical basis, with its complete phase retained.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
variable {leftCount rightCount : Nat}
variable {leftLayout : QuantumLayout leftCount} {rightLayout : QuantumLayout rightCount}

/-- Assemble arbitrary subsystem vectors in the exact basis order of an
appended physical layout. -/
@[expose] public def appendVector
    (disjoint : List.Disjoint leftLayout.identities rightLayout.identities)
    (left : HilbertVector leftLayout.register)
    (right : HilbertVector rightLayout.register) :
    HilbertVector (QuantumLayout.append leftLayout rightLayout disjoint).register :=
  HilbertVector.reindex
    (QuantumLayout.appendBasisEquiv leftLayout rightLayout disjoint).symm
    (HilbertVector.prodTensor left right)

@[simp] public theorem appendVector_apply
    (disjoint : List.Disjoint leftLayout.identities rightLayout.identities)
    (left : HilbertVector leftLayout.register)
    (right : HilbertVector rightLayout.register)
    (index : (QuantumLayout.append leftLayout rightLayout disjoint).Basis) :
    appendVector disjoint left right index =
      left (QuantumLayout.appendBasisEquiv leftLayout rightLayout disjoint index).1 *
        right (QuantumLayout.appendBasisEquiv leftLayout rightLayout disjoint index).2 := by
  rfl

/-- Appending two computational-basis vectors gives their joined physical label. -/
@[simp] public theorem appendVector_ket
    (disjoint : List.Disjoint leftLayout.identities rightLayout.identities)
    (left : leftLayout.Basis) (right : rightLayout.Basis) :
    appendVector disjoint
        (NormalizedVector.ket (R := leftLayout.register) left :
          HilbertVector leftLayout.register)
        (NormalizedVector.ket (R := rightLayout.register) right :
          HilbertVector rightLayout.register) =
      (NormalizedVector.ket
        (R := (QuantumLayout.append leftLayout rightLayout disjoint).register)
        (QuantumLayout.appendJoinBasis leftLayout rightLayout disjoint left right) :
        HilbertVector
          (QuantumLayout.append leftLayout rightLayout disjoint).register) := by
  unfold appendVector
  rw [HilbertVector.prodTensor_ket, HilbertVector.reindex_ket]
  rfl

/-- Each actual parallel-word entry is the product of the two original subsystem entries. -/
public theorem tensor_native_matrix_entry (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (disjoint : List.Disjoint leftLayout.identities rightLayout.identities)
    (row column : (QuantumLayout.append leftLayout rightLayout disjoint).Basis) :
    (tensor left right disjoint).matrix row column =
      left.matrix (QuantumLayout.appendBasisEquiv leftLayout rightLayout disjoint row).1
        (QuantumLayout.appendBasisEquiv leftLayout rightLayout disjoint column).1 *
      right.matrix (QuantumLayout.appendBasisEquiv leftLayout rightLayout disjoint row).2
        (QuantumLayout.appendBasisEquiv leftLayout rightLayout disjoint column).2 := by
  rw [tensor_embedded_matrix]
  change (∑ index : (QuantumLayout.append leftLayout rightLayout disjoint).Basis,
    (QuantumLayout.appendRightEmbedding leftLayout rightLayout disjoint).liftOperator
      right.matrix row index *
    (QuantumLayout.appendLeftEmbedding leftLayout rightLayout disjoint).liftOperator
      left.matrix index column) = _
  rw [← Equiv.sum_comp (QuantumLayout.appendBasisEquiv leftLayout rightLayout disjoint).symm]
  simp only [QuantumLayout.appendRightEmbedding_lift_entry,
    QuantumLayout.appendLeftEmbedding_lift_entry, Equiv.apply_symm_apply,
    Fintype.sum_prod_type]
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact mul_comm _ _

/-- The same actual parallel word realizes the exact tensor in the physical append basis. -/
public theorem tensor_native_matrix (left : UnitaryCircuit gates oracles leftLayout)
    (right : UnitaryCircuit gates oracles rightLayout)
    (disjoint : List.Disjoint leftLayout.identities rightLayout.identities) :
    (tensor left right disjoint).matrix =
      UnitaryOperator.reindex (QuantumLayout.appendBasisEquiv leftLayout rightLayout disjoint).symm
        (UnitaryOperator.prodTensor left.matrix right.matrix) := by
  apply Subtype.ext
  ext row column
  rw [tensor_native_matrix_entry]
  rfl

/-- The actual appended parallel word acts factorwise on arbitrary raw
subsystem vectors. -/
public theorem tensor_native_applyVec_appendVector
    (leftCircuit : UnitaryCircuit gates oracles leftLayout)
    (rightCircuit : UnitaryCircuit gates oracles rightLayout)
    (disjoint : List.Disjoint leftLayout.identities rightLayout.identities)
    (left : HilbertVector leftLayout.register)
    (right : HilbertVector rightLayout.register) :
    (tensor leftCircuit rightCircuit disjoint).matrix.applyVec
        (appendVector disjoint left right) =
      appendVector disjoint (leftCircuit.matrix.applyVec left)
        (rightCircuit.matrix.applyVec right) := by
  rw [tensor_native_matrix, appendVector, UnitaryOperator.reindex_applyVec,
    UnitaryOperator.prodTensor_applyVec_prodTensor]
  rfl

end

end QuantumAlg.UnitaryCircuit
