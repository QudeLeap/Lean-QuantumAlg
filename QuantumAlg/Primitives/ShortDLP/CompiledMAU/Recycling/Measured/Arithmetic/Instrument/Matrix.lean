/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation

/-!
# Full rectangular matrix action of each actual measured arithmetic record

The actual record-conditioned Kraus product has one common scalar on the
complete canonical control/unit/reference carrier. This is a matrix identity
of the real instrument branch, including every original Store and outcome;
it does not construct a unitary inverse of that instrument
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open MAU.Addition.Gidney.Measured.Instruction

private lemma scaled_intertwines_of_kets {R S : Register} (embedding : S.Index ↪ R.Index)
    (permutation : Equiv.Perm S.Index) (scalar : ℂ) (target : HilbertOperator R)
    (actual : ∀ column,
      target.applyVec (NormalizedVector.ket (embedding column)).vec =
        scalar • (NormalizedVector.ket (embedding (permutation column))).vec) :
    target * BasisEmbedding.matrix embedding =
      scalar • (BasisEmbedding.matrix embedding *
        (UnitaryOperator.ofPerm permutation.symm : HilbertOperator S)) := by
  classical
  ext row column
  have actualColumn := congrArg (fun vector : HilbertVector R => vector row) (actual column)
  rw [HilbertOperator.applyVec_ket] at actualColumn
  change target row (embedding column) =
    scalar * (NormalizedVector.ket (embedding (permutation column))).vec row at actualColumn
  rw [NormalizedVector.ket_apply] at actualColumn
  have leading : (target * BasisEmbedding.matrix embedding) row column =
      target row (embedding column) := by
    simp [Matrix.mul_apply, BasisEmbedding.matrix]
  have trailing : (BasisEmbedding.matrix embedding *
      (UnitaryOperator.ofPerm permutation.symm : HilbertOperator S)) row column =
      if row = embedding (permutation column) then 1 else 0 := by
    have selected (index : S.Index) : permutation.symm index = column ↔
        index = permutation column := permutation.symm_apply_eq
    simp only [Matrix.mul_apply, BasisEmbedding.matrix, UnitaryOperator.ofPerm_entry,
      selected, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact if_congr eq_comm rfl rfl
  rw [leading, Matrix.smul_apply, smul_eq_mul, trailing]
  exact actualColumn

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

variable {width} in
/-- Logical controlled unit translation leaves every external-reference coordinate unchanged. -/
def arithmeticReferencePermutation (coefficient : (ZMod modulus.toNat)ˣ) (Reference : Register) :
    Equiv.Perm ((Recycling.Carrier.full modulus.toNat).prod Reference).Index :=
  (Carrier.controlledAction modulus coefficient).prodCongr (Equiv.refl Reference.Index)

/-- Each actual record has the complete carrier/reference matrix and one common scalar. -/
lemma measuredArithmetic_record_matrix (wide : 2 ≤ width) (positive : 0 < modulus.toNat)
    (coefficient : (ZMod modulus.toNat)ˣ) (environment : model.Environment)
    (store : Store (Context base noQuantum m ell width))
    (measured : WordOutcomes (Physical.qubits width) (context_wires base noQuantum m ell width)
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val))
    (Reference : Register) :
    (wordActualKraus (operations := BitWord.model) (services := .empty)
      (Physical.qubits width) (context_wires base noQuantum m ell width)
      (ventCell base noQuantum m ell width) environment.quantum Reference
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val) store measured) *
        BasisEmbedding.matrix
          (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) =
      arithmeticAlpha width modulus coefficient •
        (BasisEmbedding.matrix
            (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) *
          (UnitaryOperator.ofPerm
            (arithmeticReferencePermutation modulus coefficient Reference).symm :
              HilbertOperator ((Recycling.Carrier.full modulus.toNat).prod Reference))) := by
  apply scaled_intertwines_of_kets
  intro column
  exact measuredArithmetic_record_ket base noQuantum m ell width modulus wide positive coefficient
    environment store measured Reference column

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
