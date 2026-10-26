/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument.Matrix

/-!
# Complete mixed/reference action of the actual measured arithmetic records

Each actual chronological record retains the full encoded density matrix,
including every off-diagonal reference entry, with its proved common scalar.
The adjoint below occurs only in the mathematical completely positive action;
it does not emit a reverse measured program [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open MAU.Addition.Gidney.Measured.Instruction

private lemma scaled_conjugation {R S : Register}
    (embedding : Matrix R.Index S.Index ℂ) (target : HilbertOperator R)
    (source density : HilbertOperator S) (scalar : ℂ)
    (actual : target * embedding = scalar • (embedding * source)) :
    target * (embedding * density * embedding.conjTranspose) * target.conjTranspose =
      (scalar * star scalar) •
        (embedding * (source * density * source.conjTranspose) * embedding.conjTranspose) := by
  have adjoints : embedding.conjTranspose * target.conjTranspose =
      star scalar • (source.conjTranspose * embedding.conjTranspose) := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul] using
      congrArg Matrix.conjTranspose actual
  calc
    _ = (target * embedding) * density *
        (embedding.conjTranspose * target.conjTranspose) := by
      simp only [Matrix.mul_assoc]
    _ = (scalar • (embedding * source)) * density *
        (star scalar • (source.conjTranspose * embedding.conjTranspose)) := by
      rw [actual, adjoints]
    _ = _ := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc,
        mul_comm (star scalar) scalar]

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- The actual branch preserves every encoded mixed/reference block with its own physical mass. -/
lemma measuredArithmetic_record_mixed (wide : 2 ≤ width) (positive : 0 < modulus.toNat)
    (coefficient : (ZMod modulus.toNat)ˣ) (environment : model.Environment)
    (store : Store (Context base noQuantum m ell width))
    (measured : WordOutcomes (Physical.qubits width) (context_wires base noQuantum m ell width)
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val))
    (Reference : Register)
    (density : HilbertOperator ((Recycling.Carrier.full modulus.toNat).prod Reference)) :
    let actual := wordActualKraus (operations := BitWord.model) (services := .empty)
      (Physical.qubits width) (context_wires base noQuantum m ell width)
      (ventCell base noQuantum m ell width) environment.quantum Reference
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val) store measured
    let embedding := BasisEmbedding.matrix
      (arithmeticJointEmbedding base noQuantum m ell width modulus Reference)
    let source : HilbertOperator ((Recycling.Carrier.full modulus.toNat).prod Reference) :=
      UnitaryOperator.ofPerm (arithmeticReferencePermutation modulus coefficient Reference).symm
    actual * (embedding * density * embedding.conjTranspose) * actual.conjTranspose =
      (arithmeticAlpha width modulus coefficient *
        star (arithmeticAlpha width modulus coefficient)) •
        (embedding * (source * density * source.conjTranspose) * embedding.conjTranspose) := by
  exact scaled_conjugation _ _ _ _ _
    (measuredArithmetic_record_matrix base noQuantum m ell width modulus wide positive coefficient
      environment store measured Reference)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
