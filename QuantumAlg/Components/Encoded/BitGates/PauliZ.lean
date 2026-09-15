/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Hadamard.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.Circuit
import all QuantumAlg.Components.Gates
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import Batteries.Data.List.Lemmas

/-!
# Addressed Pauli Z and its exact global-minus commutator

The existing Pauli-Z leaf acts on one original coordinate, with identity on
the remaining wires. The literal X, Z, X, Z sequence has full operator phase
minus one on every encoded input; this phase is retained before quantum
control, rather than discarded as a projective-state equivalence.
-/

namespace QuantumAlg.EncodedBit

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- The standard Pauli-Z leaf addressed to one encoded physical coordinate. -/
def pauliZ (target : EncodedBit encoding) : UnitaryCircuit (Qubits encoding.width) :=
  let localGate := UnitaryCircuit.ofLeaf (Gate.pauliZLeafAt [target.wire.val]) (by
    change [target.wire.val].Nodup
    simp)
  UnitaryCircuit.reindex target.targetBasisEquiv.symm
    (UnitaryCircuit.tensor localGate
      (UnitaryCircuit.identity target.RemainingRegister [] List.nodup_nil)
      { left_nodup := localGate.physical_idx_nodup
        right_nodup := List.nodup_nil
        disjoint := List.disjoint_nil_right _ })

/-- A Pauli-Z occurrence touches exactly the original target wire. -/
theorem pauliZ_physical_idx (target : EncodedBit encoding) :
    target.pauliZ.physical_idx = [target.wire.val] := rfl

/-- Pauli Z retains its existing native declaration coordinate. -/
theorem pauliZ_eventTrace (target : EncodedBit encoding) :
    target.pauliZ.eventTrace =
      [Gate.atomicEvent (.declared "QuantumAlg.Components.Gate" "pauli-z")] := rfl

private theorem pauliZ_entry (target : EncodedBit encoding)
    (row column : (Qubits encoding.width).Index) :
    target.pauliZ.matrix row column =
      Gate.ZOp (target.targetBasisEquiv row).1 (target.targetBasisEquiv column).1 *
        if (target.targetBasisEquiv row).2 = (target.targetBasisEquiv column).2
          then 1 else 0 := by
  unfold pauliZ
  rw [UnitaryCircuit.reindex_matrix, UnitaryOperator.coe_reindex,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  rfl

private theorem pauliZ_diagonal (value : Bool) :
    Gate.ZOp (finTwoEquiv.symm value) (finTwoEquiv.symm value) =
      if value then -1 else 1 := by
  cases value <;> rfl

private theorem pauliZ_offDiagonal (value : Bool) :
    Gate.ZOp (finTwoEquiv.symm (!value)) (finTwoEquiv.symm value) = 0 := by
  cases value <;> rfl

private theorem encoded_flip_ne (target : EncodedBit encoding) (state : Data) :
    encoding.encode (target.flip state) ≠ encoding.encode state := by
  intro same
  have bitSame := congrArg target.get (encoding.encode_injective same)
  rw [get_flip_self] at bitSame
  cases value : target.get state <;> simp [value] at bitSame

/-- Exact sign on each complete encoded basis label. -/
theorem pauliZ_applyVec_encoded_ket (target : EncodedBit encoding) (state : Data) :
    target.pauliZ.applyVec
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
      (if target.get state then (-1 : ℂ) else 1) •
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
  ext label
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket, pauliZ_entry]
  by_cases same : (target.targetBasisEquiv label).2 =
      (target.targetBasisEquiv (encoding.encode state)).2
  · rcases target.targetBasisEquiv_fiber state label same with original | flipped
    · subst label
      rw [targetBasisEquiv_first, pauliZ_diagonal]
      cases target.get state <;> simp [NormalizedVector.ket_apply]
    · subst label
      rw [targetBasisEquiv_flip, targetBasisEquiv_first, pauliZ_offDiagonal]
      cases target.get state <;>
        simp [NormalizedVector.ket_apply, encoded_flip_ne target state]
  · have original : label ≠ encoding.encode state := by
      intro equal
      exact same (congrArg (fun index => (target.targetBasisEquiv index).2) equal)
    cases target.get state <;> simp [same, NormalizedVector.ket_apply, original]

private theorem x_applyVec_encoded_ket (target : EncodedBit encoding) (state : Data) :
    (GateSpec.x target).program.applyVec
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
      (NormalizedVector.ket (R := Qubits encoding.width)
        (encoding.encode (target.flip state))).vec := by
  exact congrArg NormalizedVector.vec ((GateSpec.x target).realizes.apply_encoded_ket state)

/-- Four existing elementary gates implement the exact global phase minus one. -/
def globalMinus (target : EncodedBit encoding) : UnitaryCircuit (Qubits encoding.width) :=
  (((GateSpec.x target).program.seq target.pauliZ).seq
    (GateSpec.x target).program).seq target.pauliZ

/-- The complete input label is restored, with exact global phase minus one. -/
theorem globalMinus_applyVec_encoded_ket (target : EncodedBit encoding) (state : Data) :
    target.globalMinus.applyVec
        (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec =
      -(NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
  simp only [globalMinus, UnitaryCircuit.applyVec_seq]
  rw [x_applyVec_encoded_ket, pauliZ_applyVec_encoded_ket]
  simp only [UnitaryCircuit.applyVec_smul]
  rw [x_applyVec_encoded_ket, flip_flip, pauliZ_applyVec_encoded_ket, get_flip_self]
  cases target.get state <;> simp

/-- The phase correction contains exactly four actual gate events. -/
theorem globalMinus_eventTrace_length (target : EncodedBit encoding) :
    target.globalMinus.eventTrace.length = 4 := rfl

end

end QuantumAlg.EncodedBit
