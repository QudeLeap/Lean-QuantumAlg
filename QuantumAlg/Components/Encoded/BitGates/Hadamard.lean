/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Hadamard.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Util.Complex
import Batteries.Data.List.Lemmas

/-!
# A literal Hadamard on an encoded physical bit

The standard Hadamard leaf acts on the selected original wire. Tensoring
with identity on the remaining coordinates and reassembling that exact
split gives its full-register action. The construction emits one actual
Hadamard event and introduces no additional wire.
-/

namespace QuantumAlg.EncodedBit

open NormalizedVector

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The existing Hadamard gate at the target, with identity on all other coordinates. -/
def hadamard (target : EncodedBit encoding) : UnitaryCircuit (Qubits encoding.width) :=
  UnitaryCircuit.reindex target.targetBasisEquiv.symm
    (UnitaryCircuit.tensor (Gate.hadamardAt [target.wire.val] (by simp))
      (UnitaryCircuit.identity target.RemainingRegister [] List.nodup_nil)
      { left_nodup := (Gate.hadamardAt [target.wire.val] (by simp)).physical_idx_nodup
        right_nodup := List.nodup_nil
        disjoint := List.disjoint_nil_right _ })

/-- Only the actual target occurs in the gate footprint. -/
theorem hadamard_physical_idx (target : EncodedBit encoding) :
    target.hadamard.physical_idx = [target.wire.val] := by
  rfl

/-- Addressing the standard gate preserves its single native event. -/
theorem hadamard_eventTrace (target : EncodedBit encoding) :
    target.hadamard.eventTrace = [Gate.atomicEvent (.builtin "hadamard")] := by
  rfl

/-- The exact tensor-and-reindex matrix retains the other coordinates by a delta. -/
theorem hadamard_entry (target : EncodedBit encoding)
    (row column : (Qubits encoding.width).Index) :
    target.hadamard.matrix row column =
      Gate.HOp (target.targetBasisEquiv row).1 (target.targetBasisEquiv column).1 *
        if (target.targetBasisEquiv row).2 = (target.targetBasisEquiv column).2
          then 1 else 0 := by
  unfold hadamard
  rw [UnitaryCircuit.reindex_matrix, UnitaryOperator.coe_reindex,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl

private theorem hadamard_diagonal (value : Bool) :
    Gate.HOp (finTwoEquiv.symm value) (finTwoEquiv.symm value) =
      invSqrt2 * (if value then -1 else 1) := by
  cases value <;> rfl

private theorem hadamard_offDiagonal (value : Bool) :
    Gate.HOp (finTwoEquiv.symm (!value)) (finTwoEquiv.symm value) = invSqrt2 := by
  cases value <;> simp [Gate.HOp, finTwoEquiv]

private theorem encode_flip_ne (target : EncodedBit encoding) (state : Data) :
    encoding.encode (target.flip state) ≠ encoding.encode state := by
  intro same
  have bitSame := congrArg target.get (encoding.encode_injective same)
  rw [get_flip_self] at bitSame
  cases value : target.get state <;> simp [value] at bitSame

/-- Exact Hadamard superposition, including the sign for an input-one target. -/
theorem hadamard_applyVec_encoded_ket (target : EncodedBit encoding) (state : Data) :
    target.hadamard.applyVec
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
      invSqrt2 •
        ((if target.get state then (-1 : ℂ) else 1) •
            (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec +
          (NormalizedVector.ket (R := Qubits encoding.width)
            (encoding.encode (target.flip state))).vec) := by
  ext label
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket, hadamard_entry]
  by_cases same : (target.targetBasisEquiv label).2 =
      (target.targetBasisEquiv (encoding.encode state)).2
  · rcases target.targetBasisEquiv_fiber state label same with original | flipped
    · subst label
      rw [targetBasisEquiv_first, hadamard_diagonal]
      cases target.get state <;>
        simp [NormalizedVector.ket_apply, (encode_flip_ne target state).symm]
    · subst label
      rw [targetBasisEquiv_flip, targetBasisEquiv_first, hadamard_offDiagonal]
      cases target.get state <;>
        simp [NormalizedVector.ket_apply, encode_flip_ne target state]
  · have original : label ≠ encoding.encode state := by
      intro equal
      exact same (congrArg (fun index => (target.targetBasisEquiv index).2) equal)
    have flipped : label ≠ encoding.encode (target.flip state) := by
      intro equal
      apply same
      rw [equal, targetBasisEquiv_flip]
    cases target.get state <;>
      simp [same, NormalizedVector.ket_apply, original, flipped]

end

end QuantumAlg.EncodedBit
