/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.SuperdenseCoding.Construction
public import QuantumAlg.Primitives.BellPair.Construction
public import QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Algorithms.SuperdenseCoding.Construction
import all QuantumAlg.Algorithms.SuperdenseCoding.Geometry
import all QuantumAlg.Algorithms.SuperdenseCoding.Mathematics
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary.Parallel.Matrix
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Tensor.Basic
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Execution.Context.Layout.Unitary

/-!
# Source-defined full superdense-coding transformation

The shared Bell resource, mathematical decoding operator and output basis
are defined independently of the executable word. The complete native word
has this operator, and maps the entire shared resource to the decoded basis.
This exact vector equality retains relative phases between all blocks
[dW19, qcnotes.tex:879-890].
-/

namespace QuantumAlg.SuperdenseCoding.Execution
noncomputable section

open QuantumAlg.Execution Gate

/-- One binary source bit in the computational basis. -/
public def binaryBit (bit : Bool) : Fin 2 := if bit then 1 else 0

/-- The physical decoder orders its output as b,a. -/
public def blockBasis (first second : Bool) : (Qubits 2).Index :=
  prodEquiv (m := 1) (n := 1) (binaryBit second, binaryBit first)

/-- The mathematical tensor of the explicitly supplied shared Bell resources. -/
public def sharedBell : (count : Nat) → NormalizedVector (Qubits (width count))
  | 0 => NormalizedVector.ket 0
  | count + 1 => (sharedBell count).tensor bell

/-- The source-defined complete decoded basis, independent of execution. -/
public def decodedBasis : (count : Nat) → SuperdenseMessage count → (Qubits (width count)).Index
  | 0, _ => 0
  | count + 1, bits => prodEquiv
      (decodedBasis count (fun index => bits index.castSucc),
        blockBasis (bits (Fin.last count)).1 (bits (Fin.last count)).2)

/-- Mathematical encoding and decoding, tensoring the original source formula per block. -/
public def sourceOperator : (count : Nat) → SuperdenseMessage count →
    UnitaryOperator (Qubits (width count))
  | 0, _ => 1
  | count + 1, bits =>
      (sourceOperator count (fun index => bits index.castSucc)).tensor
        (superdenseDecode * superdenseEncode
          (bits (Fin.last count)).1 (bits (Fin.last count)).2)

private lemma cnot_binaryMatrix
    (environment : OracleModel.empty.Interpretation) : (cnot.binaryMatrix environment)
    = CNOTOp := by
  unfold UnitaryCircuit.binaryMatrix cnot
  rw [UnitaryCircuit.native_matrix, GateModel.Application.gateApplication_canonical_operator]
  change UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2)
    (UnitaryOperator.reindex (QuantumSignature.qubitsIndexEquiv 2).symm CNOTOp) = CNOTOp
  exact UnitaryOperator.unitaryOperator_reindex_cancel
    (QuantumSignature.qubitsIndexEquiv 2).symm _

private lemma selectedGate_binaryMatrix (bit : Bool)
    (operator : UnitaryOperator (Qubits 1)) (environment : OracleModel.empty.Interpretation) :
    ((selectedGate bit operator).binaryMatrix environment) =
      (if bit then operator else 1).tensor (1 : UnitaryOperator (Qubits 1)) := by
  cases bit with
  | true => exact Gate.singleQubitAt_first_binaryMatrix .empty 1 operator environment
  | false =>
      change ((UnitaryCircuit.identity AlgorithmGate.model .empty blockLayout).binaryMatrix
        environment) =
        (1 : UnitaryOperator (Qubits 1)).tensor (1 : UnitaryOperator (Qubits 1))
      rw [UnitaryCircuit.unitaryCircuit_binaryMatrix_identity]
      apply Subtype.ext
      exact (HilbertOperator.one_tensor_one (m := 1) (n := 1)).symm

private lemma encodingWord_binaryMatrix (first second : Bool)
    (environment : OracleModel.empty.Interpretation) :
    ((encodingWord first second).binaryMatrix environment) = superdenseEncode first second := by
  rw [encodingWord, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    selectedGate_binaryMatrix, selectedGate_binaryMatrix]
  apply Subtype.ext
  change HilbertOperator.tensor _ 1 * HilbertOperator.tensor _ 1 = _
  rw [HilbertOperator.tensor_mul_tensor, one_mul]
  rfl

private lemma decodingWord_binaryMatrix
    (environment : OracleModel.empty.Interpretation) : (decodingWord.binaryMatrix environment)
    = superdenseDecode := by
  rw [decodingWord, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq, cnot_binaryMatrix,
    Gate.singleQubitAt_first_binaryMatrix .empty 1 HOp environment]
  rfl

private lemma blockWord_binaryMatrix (first second : Bool)
    (environment : OracleModel.empty.Interpretation) :
    ((blockWord first second).binaryMatrix environment)
      = superdenseDecode * superdenseEncode first second := by
  rw [blockWord, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    decodingWord_binaryMatrix, encodingWord_binaryMatrix]

/-- The same actual parallel native word realizes the entire source operator. -/
public lemma superdense_word_binaryMatrix (count : Nat) (bits : SuperdenseMessage count)
    (environment : OracleModel.empty.Interpretation) :
    ((word count bits).binaryMatrix environment) = sourceOperator count bits := by
  induction count with
  | zero => exact UnitaryCircuit.unitaryCircuit_binaryMatrix_identity _ _ 0 environment
  | succ count ih =>
      change (((word count (fun index => bits index.castSucc)).parallelBinary
        (blockWord (bits (Fin.last count)).1 (bits (Fin.last count)).2)).binaryMatrix environment) =
        (sourceOperator count (fun index => bits index.castSucc)).tensor
          (superdenseDecode * superdenseEncode
            (bits (Fin.last count)).1 (bits (Fin.last count)).2)
      rw [UnitaryCircuit.parallelBinary_binaryMatrix,
        ih, blockWord_binaryMatrix]

private lemma block_source_correct (first second : Bool) :
    (superdenseDecode * superdenseEncode first second).applyVec
        (bell : HilbertVector (Qubits 2)) =
      (NormalizedVector.ket (blockBasis first second) : HilbertVector (Qubits 2)) := by
  rw [UnitaryOperator.mul_applyVec]
  have original := congrArg (fun state : NormalizedVector (Qubits 2) =>
    (state : HilbertVector (Qubits 2))) (superdense_coding first second)
  cases first <;> cases second <;>
    simpa [UnitaryOperator.apply_coe, blockBasis, binaryBit,
      NormalizedVector.ket0, NormalizedVector.ket1, NormalizedVector.tensor_ket] using original

/-- Every source bit pair is recovered by the joint, phase-exact mathematical operator. -/
public lemma superdense_source_correct (count : Nat) (bits : SuperdenseMessage count) :
    (sourceOperator count bits).applyVec (sharedBell count) =
      (NormalizedVector.ket (decodedBasis count bits) : HilbertVector (Qubits (width count))) := by
  induction count with
  | zero => exact UnitaryOperator.one_applyVec _
  | succ count ih =>
      change ((sourceOperator count (fun index => bits index.castSucc)).tensor
        (superdenseDecode * superdenseEncode
          (bits (Fin.last count)).1 (bits (Fin.last count)).2)).applyVec
          (HilbertVector.tensor (sharedBell count) bell) =
        (NormalizedVector.ket (R := Qubits (width count + 2))
          (prodEquiv (m := width count) (n := 2)
            (decodedBasis count (fun index => bits index.castSucc),
              blockBasis (bits (Fin.last count)).1 (bits (Fin.last count)).2)) :
          HilbertVector (Qubits (width count + 2)))
      rw [UnitaryOperator.tensor_applyVec_tensor, ih, block_source_correct]
      exact congrArg (fun state : NormalizedVector (Qubits (width count + 2)) =>
        (state : HilbertVector (Qubits (width count + 2))))
        (NormalizedVector.tensor_ket _ _)

/-- Binary labels placed on the original complete physical context. -/
public def physicalBasis (count : Nat) :
    (Qubits (width count)).Index ≃ (context count).register.Index :=
  (QuantumSignature.qubitsIndexEquiv (width count)).symm.trans
    (basisOfEqualWires _ _ (context_wires count))

/-- The initial physical resource is an independently specified tensor of Bell states. -/
public def initialState (count : Nat) : NormalizedVector (context count).register :=
  NormalizedVector.reindex (physicalBasis count) (sharedBell count)

/-- Independent complete quantum output, with no state or budget extracted from a run. -/
public def finalBasis (count : Nat) (bits : SuperdenseMessage count) :
    (context count).register.Index := physicalBasis count (decodedBasis count bits)

/-- Independent full operator on the original systems. -/
public def physicalOperator (count : Nat) (bits : SuperdenseMessage count) :
    UnitaryOperator (context count).register :=
  UnitaryOperator.reindex (physicalBasis count) (sourceOperator count bits)

/-- All off-diagonal entries of the actual placed word match the source operator. -/
public lemma superdense_placed_matrix (count : Nat) (bits : SuperdenseMessage count)
    (environment : OracleModel.empty.Interpretation) :
    ((placedWord count bits).matrix environment) = physicalOperator count bits := by
  have same := congrArg (UnitaryOperator.reindex
    (QuantumSignature.qubitsIndexEquiv (width count)).symm)
    (superdense_word_binaryMatrix count bits environment)
  rw [UnitaryCircuit.binaryMatrix, UnitaryOperator.unitaryOperator_reindex_cancel] at same
  rw [placedWord, unitaryOfEqualWires_matrix, same,
    UnitaryOperator.unitaryOperator_reindex_trans]
  rfl

/-- The full physical output before measurement is the independent decoded basis vector. -/
public lemma superdense_physical_correct (count : Nat) (bits : SuperdenseMessage count) :
    (physicalOperator count bits).applyVec (initialState count) =
      (NormalizedVector.ket (finalBasis count bits) : HilbertVector (context count).register) := by
  change (UnitaryOperator.reindex (physicalBasis count) (sourceOperator count bits)).applyVec
    (HilbertVector.reindex (physicalBasis count) (sharedBell count)) = _
  rw [UnitaryOperator.reindex_applyVec, superdense_source_correct, HilbertVector.reindex_ket]
  rfl

end
end QuantumAlg.SuperdenseCoding.Execution
