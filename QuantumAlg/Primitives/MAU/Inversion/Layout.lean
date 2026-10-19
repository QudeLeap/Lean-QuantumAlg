/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Primitives.Arithmetic.BitSlice
import all QuantumAlg.Primitives.Arithmetic.Comparator
import all QuantumAlg.Primitives.Arithmetic.PlainAdder
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.Schedule.ZeroTestValue
import all QuantumAlg.Primitives.Arithmetic.PlainAdder.StructuredCircuit
import all QuantumAlg.Primitives.MAU.Addition.VBE.Circuit
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Util.ZModUnits
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Primitives.MAU.Addition.StructuredCircuit
import all QuantumAlg.Primitives.MAU.Inversion.Basic
import all QuantumAlg.Primitives.MAU.Inversion.Schedule

/-!
# Modular-inversion staged-state encodings

This module provides layout hooks for modular-inversion same-Circuit witnesses:
faithful binary encodings for the staged state space used by the fixed-round
Montgomery-Kaliski route [RNSL17, ECDLP.tex:390-465,753-755].
-/

section

namespace QuantumAlg
namespace MAU.Inversion
namespace StageState

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

/-- Product view of the staged modular-inversion state. -/
def tupleEquiv (N : Nat) :
    StageState N ≃ ((ZMod N)ˣ × (ZMod N × (ZMod N × Bool))) where
  toFun := fun s => (s.input, (s.target, (s.inverseScratch, s.flag)))
  invFun := fun x =>
    { input := x.1
      target := x.2.1
      inverseScratch := x.2.2.1
      flag := x.2.2.2 }
  left_inv := by
    intro s
    cases s
    rfl
  right_inv := by
    intro x
    rcases x with ⟨input, rest⟩
    rcases rest with ⟨target, rest'⟩
    rcases rest' with ⟨inverseScratch, flag⟩
    rfl

/-- Field-by-field binary encoding for the staged state: unit input, target,
inverse scratch, and one cleanup flag. -/
def fieldTupleEncoding {N n : Nat} (E : BinaryResidueEncoding N n) :
    BinaryLabelEncoding ((ZMod N)ˣ × (ZMod N × (ZMod N × Bool))) :=
  BinaryLabelEncoding.prod (BinaryLabelEncoding.ofUnitResidueEncoding E)
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
        BinaryLabelEncoding.bool))

/-- Faithful field-by-field binary encoding of staged modular-inversion states. -/
def fieldEncoding {N n : Nat} (E : BinaryResidueEncoding N n) :
    BinaryLabelEncoding (StageState N) :=
  (fieldTupleEncoding E).relabel (tupleEquiv N)

/-- Faithful binary encoding of the staged modular-inversion state space from
any cardinality bound `Fintype.card (StageState N) <= 2^width`.  Later concrete
wire-slice layouts can replace this finite-state enumeration while preserving
the same `BinaryLabelEncoding` interface. -/
def encodingOfCardBound {N : Nat} [NeZero N] (width : Nat)
    (hcard : Fintype.card (StageState N) <= 2 ^ width) :
    BinaryLabelEncoding (StageState N) :=
  BinaryLabelEncoding.ofFintypeCardLe (StageState N) width hcard

@[simp] lemma encodingOfCardBound_width {N : Nat} [NeZero N]
    (width : Nat) (hcard : Fintype.card (StageState N) <= 2 ^ width) :
    (encodingOfCardBound (N := N) width hcard).width = width :=
  rfl

@[simp] lemma fieldTupleEncoding_width {N n : Nat}
    (E : BinaryResidueEncoding N n) :
    (fieldTupleEncoding E).width = n + (n + (n + 1)) :=
  rfl

@[simp] lemma fieldEncoding_width {N n : Nat}
    (E : BinaryResidueEncoding N n) :
    (fieldEncoding E).width = n + (n + (n + 1)) :=
  rfl

@[simp] lemma fieldEncoding_encode {N n : Nat}
    (E : BinaryResidueEncoding N n) (s : StageState N) :
    (fieldEncoding E).encode s =
      (fieldTupleEncoding E).encode
        (s.input, (s.target, (s.inverseScratch, s.flag))) :=
  rfl

/-! ### Field wire slices -/

/-- Wire address for a bit of the unit-input field. -/
def inputWire {N n : Nat} (E : BinaryResidueEncoding N n) (bit : Fin n) :
    Fin (fieldEncoding E).width :=
  ⟨bit.val, by
    have hbit := bit.isLt
    simp [fieldEncoding, fieldTupleEncoding]
    omega⟩

/-- Wire address for a bit of the target-accumulator field. -/
def targetWire {N n : Nat} (E : BinaryResidueEncoding N n) (bit : Fin n) :
    Fin (fieldEncoding E).width :=
  ⟨n + bit.val, by
    have hbit := bit.isLt
    simp [fieldEncoding, fieldTupleEncoding]
    omega⟩

/-- Wire address for a bit of the inverse-scratch field. -/
def inverseScratchWire {N n : Nat} (E : BinaryResidueEncoding N n)
    (bit : Fin n) : Fin (fieldEncoding E).width :=
  ⟨n + n + bit.val, by
    have hbit := bit.isLt
    rw [fieldEncoding_width]
    omega⟩

/-- Wire address for the one-bit cleanup flag field. -/
def flagWire {N n : Nat} (E : BinaryResidueEncoding N n) :
    Fin (fieldEncoding E).width :=
  ⟨n + n + n, by
    rw [fieldEncoding_width]
    omega⟩

@[simp] lemma inputWire_val {N n : Nat} (E : BinaryResidueEncoding N n)
    (bit : Fin n) :
    (inputWire E bit).val = bit.val :=
  rfl

@[simp] lemma targetWire_val {N n : Nat} (E : BinaryResidueEncoding N n)
    (bit : Fin n) :
    (targetWire E bit).val = n + bit.val :=
  rfl

@[simp] lemma inverseScratchWire_val {N n : Nat}
    (E : BinaryResidueEncoding N n) (bit : Fin n) :
    (inverseScratchWire E bit).val = n + n + bit.val :=
  rfl

@[simp] lemma flagWire_val {N n : Nat} (E : BinaryResidueEncoding N n) :
    (flagWire E).val = n + n + n :=
  rfl

/-! ### Field-level encoded bits -/

/-- Encoded bit for the cleanup flag inside the product tuple layout. -/
def tupleFlagBit {N n : Nat} (E : BinaryResidueEncoding N n) :
    EncodedBit (fieldTupleEncoding E) :=
  BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.ofUnitResidueEncoding E)
    (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
        BinaryLabelEncoding.bool))
    (BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.ofResidueEncoding E)
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.ofResidueEncoding E)
        BinaryLabelEncoding.bool)
      (BinaryLabelEncoding.prodRightBit (BinaryLabelEncoding.ofResidueEncoding E)
        BinaryLabelEncoding.bool BinaryLabelEncoding.boolBit))

/-- Encoded bit for the cleanup flag inside the staged-state field encoding. -/
def flagBit {N n : Nat} (E : BinaryResidueEncoding N n) :
    EncodedBit (fieldEncoding E) :=
  (tupleFlagBit E).relabel (tupleEquiv N)

/-- Toggle only the cleanup flag of a staged inversion state. -/
def toggleFlag {N : Nat} (s : StageState N) : StageState N where
  input := s.input
  target := s.target
  inverseScratch := s.inverseScratch
  flag := !s.flag

@[simp] lemma flagBit_flip {N n : Nat} (E : BinaryResidueEncoding N n)
    (s : StageState N) :
    (flagBit E).flip s = toggleFlag s := by
  cases s
  rfl

/-- One X gate on the field-encoded cleanup flag. -/
def toggleFlagProgram {N n : Nat} (E : BinaryResidueEncoding N n) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (fieldEncoding E).width).toQuantum :=
  (QubitPrimitive.x (flagBit E).wire).circuit (QubitLayout.canonical _) .empty

/-- The flag X gate realizes cleanup-flag toggling on the same field encoding. -/
lemma toggleFlagProgram_realizes {N n : Nat}
    (E : BinaryResidueEncoding N n) :
    UnitaryCircuit.Realizes (fieldEncoding E) (toggleFlagProgram E) environment
      toggleFlag where
  apply_encoded_ket := by
    intro s
    simpa [toggleFlagProgram] using
      (EncodedBit.x_realizes (environment := environment) (flagBit E)).apply_encoded_ket s

end

end StageState
end MAU.Inversion
end QuantumAlg

end
