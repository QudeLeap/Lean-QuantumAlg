/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Hadamard.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Gates.SingleQubit.Entries
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Base.Layout.Qubit.Quantum
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Util.Complex

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

/-- One actual native Hadamard at the original encoded physical position. -/
def hadamard (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (oracles : OracleModel) : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  Gate.singleQubitAt layout.toQuantum oracles Gate.HOp target.wire rfl

/-- The default model charges the actual Hadamard as one single-qubit instruction. -/
lemma hadamard_eventTrace (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (oracles : OracleModel) :
    (target.hadamard layout oracles).eventTrace = [.gate .singleQubit] := rfl

private lemma complement_eq_iff (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (row column : Fin encoding.width → Fin 2) :
    let application := Gate.singleQubitApplication layout.toQuantum Gate.HOp target.wire rfl
    (application.basisEquiv row).2 = (application.basisEquiv column).2 ↔
      (target.targetBasisEquiv (layout.basisEquiv row)).2 =
        (target.targetBasisEquiv (layout.basisEquiv column)).2 := by
  let application := Gate.singleQubitApplication layout.toQuantum Gate.HOp target.wire rfl
  have member (index : Fin encoding.width) :
      index ∈ application.embedding.selection ↔ index = target.wire := by
    change index ∈ Finset.univ.map
      (⟨fun _ : Fin 1 => target.wire,
        fun _ _ _ => Subsingleton.elim _ _⟩ : Fin 1 ↪ Fin encoding.width) ↔ _
    constructor
    · intro selected
      rcases Finset.mem_map.mp selected with ⟨position, _, equal⟩
      exact equal.symm
    · intro equal
      exact Finset.mem_map.mpr ⟨0, Finset.mem_univ _, equal.symm⟩
  have coordinates (basis : Fin encoding.width → Fin 2) :
      (target.targetBasisEquiv (layout.basisEquiv basis)).2 =
        fun index : {wire : Fin encoding.width // wire ≠ target.wire} => basis index.val := by
    change ((Equiv.funSplitAt target.wire (Fin 2))
      ((BinaryBasis.bigEndianEquiv encoding.width).symm
        ((BinaryBasis.bigEndianEquiv encoding.width) basis))).2 = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [coordinates row, coordinates column]
  constructor
  · intro same
    funext index
    exact congrFun same ⟨index.val, Finset.mem_compl.mpr
      (fun selected => index.property ((member index.val).mp selected))⟩
  · intro same
    funext index
    exact congrFun same ⟨index.val, fun equal =>
      (Finset.mem_compl.mp index.property) ((member index.val).mpr equal)⟩

/-- Every other original wire is retained in the exact native matrix entry. -/
lemma hadamard_entry (target : EncodedBit encoding) (layout : QubitLayout encoding.width)
    (oracles : OracleModel) {environment : oracles.Interpretation}
    (row column : Fin encoding.width → Fin 2) :
    ((target.hadamard layout oracles).matrix environment) row column =
      Gate.HOp (row target.wire) (column target.wire) *
        if (target.targetBasisEquiv (layout.basisEquiv row)).2 =
            (target.targetBasisEquiv (layout.basisEquiv column)).2 then 1 else 0 := by
  classical
  refine (Gate.singleQubitAt_matrix_entry layout.toQuantum oracles Gate.HOp
    target.wire rfl row column environment).trans ?_
  exact congrArg (fun value : ℂ => Gate.HOp (row target.wire) (column target.wire) * value)
    (if_congr (complement_eq_iff target layout row column) rfl rfl)

private lemma hadamard_diagonal (value : Bool) :
    Gate.HOp (finTwoEquiv.symm value) (finTwoEquiv.symm value) =
      invSqrt2 * (if value then -1 else 1) := by
  cases value <;> rfl

private lemma hadamard_offDiagonal (value : Bool) :
    Gate.HOp (finTwoEquiv.symm (!value)) (finTwoEquiv.symm value) = invSqrt2 := by
  cases value <;> simp [Gate.HOp, finTwoEquiv]

private lemma encode_flip_ne (target : EncodedBit encoding) (state : Data) :
    encoding.encode (target.flip state) ≠ encoding.encode state := by
  intro same
  have bitSame := congrArg target.get (encoding.encode_injective same)
  rw [get_flip_self] at bitSame
  cases value : target.get state <;> simp [value] at bitSame

/-- Exact full-register superposition, including the sign for an input-one target. -/
lemma hadamard_applyVec_encoded_ket (target : EncodedBit encoding)
    (layout : QubitLayout encoding.width) (oracles : OracleModel) {environment :
      oracles.Interpretation}
    (state : Data) :
    (target.hadamard layout oracles).applyVec environment
        (NormalizedVector.ket (R := layout.toQuantum.register)
          (layout.basisEquiv.symm (encoding.encode state))).vec =
      invSqrt2 •
        ((if target.get state then (-1 : ℂ) else 1) •
            (NormalizedVector.ket (R := layout.toQuantum.register)
              (layout.basisEquiv.symm (encoding.encode state))).vec +
          (NormalizedVector.ket (R := layout.toQuantum.register)
            (layout.basisEquiv.symm (encoding.encode (target.flip state)))).vec) := by
  classical
  ext row
  refine (HilbertOperator.applyVec_ket (R := layout.toQuantum.register)
    ((target.hadamard layout oracles).matrix environment)
    (layout.basisEquiv.symm (encoding.encode state)) row).trans ?_
  refine (hadamard_entry target layout oracles row
    (layout.basisEquiv.symm (encoding.encode state))).trans ?_
  rw [Equiv.apply_symm_apply]
  have first (label : Fin encoding.width → Fin 2) :
      label target.wire = (target.targetBasisEquiv (layout.basisEquiv label)).1 := by
    change label target.wire =
      ((BinaryBasis.bigEndianEquiv encoding.width).symm
        ((BinaryBasis.bigEndianEquiv encoding.width) label)) target.wire
    rw [Equiv.symm_apply_apply]
  have ket_value (label : Fin encoding.width → Fin 2) :
      (NormalizedVector.ket (R := layout.toQuantum.register) label).vec row =
        if row = label then (1 : ℂ) else 0 := by
    refine (NormalizedVector.ket_apply (R := layout.toQuantum.register) label row).trans ?_
    split_ifs <;> rfl
  change Gate.HOp (row target.wire)
      (layout.basisEquiv.symm (encoding.encode state) target.wire) *
      (if (target.targetBasisEquiv (layout.basisEquiv row)).2 =
        (target.targetBasisEquiv (encoding.encode state)).2 then 1 else 0) =
    invSqrt2 * ((if target.get state then (-1 : ℂ) else 1) *
      (NormalizedVector.ket (R := layout.toQuantum.register)
        (layout.basisEquiv.symm (encoding.encode state))).vec row +
      (NormalizedVector.ket (R := layout.toQuantum.register)
        (layout.basisEquiv.symm (encoding.encode (target.flip state)))).vec row)
  refine Eq.trans ?_ (congrArg₂
    (fun left right : ℂ => invSqrt2 * ((if target.get state then (-1 : ℂ) else 1) * left + right))
    (ket_value (layout.basisEquiv.symm (encoding.encode state)))
    (ket_value (layout.basisEquiv.symm (encoding.encode (target.flip state))))).symm
  rw [first row, first (layout.basisEquiv.symm (encoding.encode state)),
    Equiv.apply_symm_apply]
  by_cases same : (target.targetBasisEquiv (layout.basisEquiv row)).2 =
      (target.targetBasisEquiv (encoding.encode state)).2
  · rcases target.targetBasisEquiv_fiber state (layout.basisEquiv row) same with original | flipped
    · have equal : row = layout.basisEquiv.symm (encoding.encode state) :=
        (layout.basisEquiv.eq_symm_apply).mpr original
      subst row
      rw [Equiv.apply_symm_apply, targetBasisEquiv_first, hadamard_diagonal]
      have different := fun equal => encode_flip_ne target state
        (layout.basisEquiv.symm.injective equal)
      cases target.get state <;> simp [Ne.symm different]
    · have equal : row = layout.basisEquiv.symm (encoding.encode (target.flip state)) :=
        (layout.basisEquiv.eq_symm_apply).mpr flipped
      subst row
      rw [Equiv.apply_symm_apply, targetBasisEquiv_flip, targetBasisEquiv_first,
        hadamard_offDiagonal]
      cases target.get state <;> simp [encode_flip_ne target state]
  · have original : row ≠ layout.basisEquiv.symm (encoding.encode state) := by
      intro equal
      apply same
      rw [equal, Equiv.apply_symm_apply]
    have flipped : row ≠ layout.basisEquiv.symm (encoding.encode (target.flip state)) := by
      intro equal
      apply same
      rw [equal, Equiv.apply_symm_apply, targetBasisEquiv_flip]
    simp [same, original, flipped]

end

end QuantumAlg.EncodedBit
