/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Control
import all QuantumAlg.Core.Base.Tensor.Reference

/-!
# Full actual readout matrix and its independent logical H/reset operator

The rectangular matrix identity includes every physical row and all reference
entries. The logical row is the ordinary H followed by the selected reset
block, and is derived from the actual physical outcome character
[G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open EncodedBit.MeasuredUncompute
open scoped Kronecker

private lemma hadamard_character (outcome bit : Fin 2) :
    Gate.HOp outcome bit = NormalizedVector.invSqrt2 * character outcome (finTwoEquiv bit) := by
  fin_cases outcome <;> fin_cases bit <;> simp [Gate.HOp, character, finTwoEquiv]

/-- Independent H followed by the selected logical control reset beside an untouched reference. -/
def readoutSource {S : Register} (outcome : Fin 2) (Reference : Register) :
    HilbertOperator (((Qubits 1).prod S).prod Reference) :=
  (ControlKraus.resetBlock (S := S) outcome *
    (ControlKraus.hadamard (S := S) : HilbertOperator ((Qubits 1).prod S))) ⊗ₖ
      (1 : HilbertOperator Reference)

private lemma readoutSource_entry {S : Register} (outcome : Fin 2) (Reference : Register)
    (row column : (((Qubits 1).prod S).prod Reference).Index) :
    readoutSource (S := S) outcome Reference row column =
      if row = ((0, column.1.2), column.2) then
        NormalizedVector.invSqrt2 * character outcome (finTwoEquiv column.1.1) else 0 := by
  classical
  rcases row with ⟨⟨rowBit, rowSeed⟩, rowReference⟩
  rcases column with ⟨⟨columnBit, columnSeed⟩, columnReference⟩
  have localEntry :
      (ControlKraus.resetBlock (S := S) outcome *
        (ControlKraus.hadamard (S := S) : HilbertOperator ((Qubits 1).prod S)))
          (rowBit, rowSeed) (columnBit, columnSeed) =
        if rowBit = 0 then Gate.HOp outcome columnBit *
          (if rowSeed = columnSeed then 1 else 0) else 0 := by
    rw [ControlKraus.hadamard, unitaryOperator_prodTensor_identity, Matrix.mul_apply]
    change (∑ middle : Fin 2 × S.Index,
      (if rowBit = 0 ∧ middle.1 = outcome then
        (if rowSeed = middle.2 then (1 : ℂ) else 0) else 0) *
      (Gate.HOp middle.1 columnBit * (if middle.2 = columnSeed then 1 else 0))) = _
    fin_cases outcome <;> simp [Fintype.sum_prod_type]
  have samePair :
      (((rowBit, rowSeed), rowReference) : (((Qubits 1).prod S).prod Reference).Index) =
          ((0, columnSeed), columnReference) ↔
        rowBit = 0 ∧ rowSeed = columnSeed ∧ rowReference = columnReference := by
    constructor
    · intro same
      exact ⟨congrArg (fun entry => entry.1.1) same,
        congrArg (fun entry => entry.1.2) same, congrArg Prod.snd same⟩
    · rintro ⟨rfl, rfl, rfl⟩
      rfl
  rw [readoutSource, Matrix.kronecker_apply, localEntry, hadamard_character]
  simp only [samePair, Matrix.one_apply]
  split_ifs <;> simp_all

private lemma intertwines_of_ket_images {R S : Register} (embedding : S.Index ↪ R.Index)
    (target : HilbertOperator R) (source : HilbertOperator S)
    (image : S.Index → S.Index) (scalar : S.Index → ℂ)
    (actual : ∀ column,
      target.applyVec (NormalizedVector.ket (embedding column)).vec =
        scalar column • (NormalizedVector.ket (embedding (image column))).vec)
    (sourceEntry : ∀ row column,
      source row column = if row = image column then scalar column else 0) :
    target * BasisEmbedding.matrix embedding = BasisEmbedding.matrix embedding * source := by
  classical
  ext row column
  have actualColumn := congrArg (fun vector : HilbertVector R => vector row) (actual column)
  rw [HilbertOperator.applyVec_ket] at actualColumn
  change target row (embedding column) =
    scalar column * (NormalizedVector.ket (embedding (image column))).vec row at actualColumn
  rw [NormalizedVector.ket_apply] at actualColumn
  have left : (target * BasisEmbedding.matrix embedding) row column =
      target row (embedding column) := by
    simp [Matrix.mul_apply, BasisEmbedding.matrix]
  have right : (BasisEmbedding.matrix embedding * source) row column =
      if row = embedding (image column) then scalar column else 0 := by
    simp [Matrix.mul_apply, BasisEmbedding.matrix, sourceEntry, eq_comm]
  rw [left, right]
  simpa only [mul_ite, mul_one, mul_zero] using actualColumn

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- The real readout matrix agrees with the independent logical H/reset on every carrier column. -/
lemma readout_record_matrix (environment : OracleModel.empty.Interpretation)
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) (Reference : Register) :
    krausOperator (oracles := .empty) (control base noQuantum m ell width)
        (control_qubit base noQuantum m ell width) environment outcome Reference *
      BasisEmbedding.matrix
        (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) =
    BasisEmbedding.matrix
        (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) *
      readoutSource (S := Recycling.Carrier.units modulus.toNat)
        (placedOutcome (Physical.layout width).control (Physical.qubits width)
          (Context base noQuantum m ell width) (context_wires base noQuantum m ell width) outcome)
        Reference := by
  apply intertwines_of_ket_images
    (R := (Context base noQuantum m ell width).register.prod Reference)
    (S := (Recycling.Carrier.full modulus.toNat).prod Reference) _ _ _
    (fun column => ((0, column.1.2), column.2))
    (fun column => NormalizedVector.invSqrt2 * character
      (placedOutcome (Physical.layout width).control (Physical.qubits width)
        (Context base noQuantum m ell width) (context_wires base noQuantum m ell width) outcome)
      (finTwoEquiv column.1.1))
  · exact readout_record_ket base noQuantum m ell width modulus environment outcome Reference
  · exact readoutSource_entry _ Reference

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
