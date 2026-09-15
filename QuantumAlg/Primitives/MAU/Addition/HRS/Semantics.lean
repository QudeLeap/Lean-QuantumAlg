/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Primitives.MAU.Addition.HRS.OneDirty
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Certified

public import QuantumAlg.Primitives.MAU.Addition.WordTranslation
import all QuantumAlg.Primitives.MAU.Addition.WordTranslation

/-!
# Exact HRS action on the word and its borrowed bit

The independent operator is finite-word translation tensored with identity
on the one borrowed bit. Equality of the actual recursive program with this
operator preserves its phase and arbitrary joint input correlations
[HRS16, paper.tex:175-177,232-260].
-/

namespace QuantumAlg.MAU.Addition.HRS

noncomputable section

/-- Independent constant addition and the identity on the supplied borrowed bit. -/
public def oneDirtyOperator (width : Nat) (constant : Fin (2 ^ width)) :
    UnitaryOperator (Qubits (width + 1)) :=
  (wordTranslation width constant.val).tensor (1 : UnitaryOperator (Qubits 1))

private theorem identity_apply (state : NormalizedVector (Qubits 1)) :
    (1 : UnitaryOperator (Qubits 1)).apply state = state := by
  apply NormalizedVector.ext
  intro index
  exact congrArg (fun vector : HilbertVector (Qubits 1) => vector index)
    (UnitaryOperator.one_applyVec (state : HilbertVector (Qubits 1)))

/-- On arbitrary tensor inputs the borrowed state is unchanged; the full matrix law
below also covers non-product joint inputs. -/
public theorem oneDirtyOperator_tensor (width : Nat) (constant : Fin (2 ^ width))
    (word : NormalizedVector (Qubits width)) (borrowed : NormalizedVector (Qubits 1)) :
    (oneDirtyOperator width constant).apply (word.tensor borrowed) =
      ((wordTranslation width constant.val).apply word).tensor borrowed := by
  rw [oneDirtyOperator, UnitaryOperator.tensor_apply_tensor, identity_apply]

private theorem encoding_ket (width : Nat) (input : Fin (2 ^ width)) (dirty : Bool) :
    NormalizedVector.ket (R := Qubits (oneDirtyEncoding width).width)
      ((oneDirtyEncoding width).encode (input, dirty)) =
      (NormalizedVector.ket input).tensor
        (NormalizedVector.ket (R := Qubits 1) (BinaryLabelEncoding.bool.encode dirty)) :=
  (NormalizedVector.tensor_ket input (BinaryLabelEncoding.bool.encode dirty)).symm

private theorem operator_encoded_ket (width : Nat) (constant input : Fin (2 ^ width))
    (dirty : Bool) :
    (oneDirtyOperator width constant).apply
      (NormalizedVector.ket ((oneDirtyEncoding width).encode (input, dirty))) =
      NormalizedVector.ket ((oneDirtyEncoding width).encode (addWord constant input, dirty)) := by
  have tensorAction := oneDirtyOperator_tensor width constant (NormalizedVector.ket input)
    (NormalizedVector.ket (R := Qubits 1) (BinaryLabelEncoding.bool.encode dirty))
  rw [wordTranslation_ket] at tensorAction
  exact (congrArg (oneDirtyOperator width constant).apply (encoding_ket width input dirty)).trans
    (tensorAction.trans (encoding_ket width (addWord constant input) dirty).symm)

private def encodingEquiv (width : Nat) :
    OneDirtyRegisters width ≃ Fin (2 ^ (width + 1)) :=
  (Equiv.prodCongr (Equiv.refl (Fin (2 ^ width))) finTwoEquiv.symm).trans
    (prodEquiv (m := width) (n := 1))

private theorem encodingEquiv_apply (width : Nat) (state : OneDirtyRegisters width) :
    encodingEquiv width state = (oneDirtyEncoding width).encode state := by
  rcases state with ⟨input, dirty⟩
  cases dirty <;> rfl

/-- The actual recursive HRS circuit is exactly translation tensored with borrowed identity. -/
theorem hrsOneDirty_matrix (width : Nat) (constant : Fin (2 ^ width)) :
    (oneDirtyProgram width constant).matrix = oneDirtyOperator width constant := by
  apply Subtype.ext
  ext output input
  obtain ⟨⟨word, dirty⟩, rfl⟩ := (encodingEquiv width).surjective input
  rw [encodingEquiv_apply]
  have actual := congrArg (fun state : NormalizedVector (Qubits (width + 1)) => state output)
    (hrsOneDirty_apply width constant word dirty)
  have semantic := congrArg (fun state : NormalizedVector (Qubits (width + 1)) => state output)
    (operator_encoded_ket width constant word dirty)
  have actualColumn :=
    (HilbertOperator.applyVec_ket
      ((oneDirtyProgram width constant).matrix :
        HilbertOperator (Qubits (oneDirtyEncoding width).width))
      ((oneDirtyEncoding width).encode (word, dirty)) output).symm.trans actual
  have semanticColumn :=
    (HilbertOperator.applyVec_ket
      (oneDirtyOperator width constant : HilbertOperator (Qubits (width + 1)))
      ((oneDirtyEncoding width).encode (word, dirty)) output).symm.trans semantic
  exact actualColumn.trans semanticColumn.symm

end

end QuantumAlg.MAU.Addition.HRS
