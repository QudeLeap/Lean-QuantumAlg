/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Native.Branch
import all QuantumAlg.Primitives.QFT.Source
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Persistent unnormalized accumulator/reference trajectories

Every factor is the actual native branch
derived in NativeBranch. The same unit accumulator and the same arbitrary
reference occur in every factor, including the boundary between the two
exponents. No independence or per-bit initialization is assumed. The source
matrix is unnormalized throughout: sigma_y is updated by B_y sigma B_y^*.

The chronological output record determines each feedback angle from earlier
bits of its own exponent. This module describes record-conditioned native
operators; connecting those records to the actual retained Store/history
instrument remains a separate execution theorem, not a premise below.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Trajectory

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open scoped Kronecker

variable {width : Nat} (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]
  (positive : 0 < modulus.val)

/-- A native stage choice consists of real gate parameters and its measured finite outcome. -/
structure Choice where
  coefficient : (ZMod modulus.val)ˣ
  angle : ℝ
  outcome : Fin 2

def nativeFactor (Reference : Register) (choice : Choice modulus) :
    HilbertOperator ((Carrier.physical width).prod Reference) :=
  NativeBranch.operator (environment := environment) modulus choice.coefficient choice.angle
    choice.outcome ⊗ₖ
    (1 : HilbertOperator Reference)

def sourceFactor (Reference : Register) (choice : Choice modulus) :
    HilbertOperator ((Carrier.units modulus.val).prod Reference) :=
  ControlKraus.halfSum (Carrier.translation modulus choice.coefficient :
    HilbertOperator (Carrier.units modulus.val))
      (Complex.exp ((choice.angle : ℂ) * Complex.I)) choice.outcome ⊗ₖ
        (1 : HilbertOperator Reference)

/-- Chronological products apply the head first, so its factor is rightmost. -/
def nativeProduct (Reference : Register) : List (Choice modulus) →
    HilbertOperator ((Carrier.physical width).prod Reference)
  | [] => 1
  | head :: tail => nativeProduct Reference tail * nativeFactor (environment := environment)
    modulus Reference head

def sourceProduct (Reference : Register) : List (Choice modulus) →
    HilbertOperator ((Carrier.units modulus.val).prod Reference)
  | [] => 1
  | head :: tail => sourceProduct Reference tail * sourceFactor modulus Reference head

/-- The unnormalized posterior passes directly into the next actual controlled multiplier. -/
def σ (Reference : Register) : List (Choice modulus) →
    HilbertOperator ((Carrier.units modulus.val).prod Reference) →
      HilbertOperator ((Carrier.units modulus.val).prod Reference)
  | [], density => density
  | head :: tail, density =>
      let b := sourceFactor modulus Reference head
      σ Reference tail (b * density * b.conjTranspose)

/-- This equality retains every off-diagonal entry, rather than just branch mass. -/
lemma sigma_eq_product (Reference : Register) (choices : List (Choice modulus))
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    σ modulus Reference choices density =
      sourceProduct modulus Reference choices * density *
        (sourceProduct modulus Reference choices).conjTranspose := by
  induction choices generalizing density with
  | nil => simp only [σ, sourceProduct, Matrix.one_mul, Matrix.conjTranspose_one,
      Matrix.mul_one]
  | cons head tail induction =>
      simp only [σ, sourceProduct, induction, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Actual control reset makes the same zero-control carrier available at every step. -/
lemma nativeProduct_intertwines (Reference : Register) (choices : List (Choice modulus)) :
    nativeProduct (environment := environment) modulus Reference choices *
        BasisEmbedding.matrix
          (BasisEmbedding.withReference (Carrier.zeroEmbedding modulus positive) Reference) =
      BasisEmbedding.matrix
          (BasisEmbedding.withReference (Carrier.zeroEmbedding modulus positive) Reference) *
        sourceProduct modulus Reference choices := by
  let j := BasisEmbedding.matrix
    (BasisEmbedding.withReference (Carrier.zeroEmbedding modulus positive) Reference)
  induction choices with
  | nil => simp only [nativeProduct, sourceProduct, Matrix.one_mul, Matrix.mul_one]
  | cons head tail induction =>
      have step : nativeFactor (environment := environment) modulus Reference head * j =
          j * sourceFactor modulus Reference head :=
        NativeBranch.operator_zero_intertwines_reference modulus positive
          head.coefficient head.angle head.outcome Reference
      change (nativeProduct (environment := environment) modulus Reference tail * nativeFactor
        (environment := environment) modulus Reference head) * j =
        j * (sourceProduct modulus Reference tail * sourceFactor modulus Reference head)
      calc
        _ = nativeProduct (environment := environment) modulus Reference tail * (nativeFactor
          (environment := environment) modulus Reference head * j) := by
          rw [Matrix.mul_assoc]
        _ = nativeProduct (environment := environment) modulus Reference tail * (j * sourceFactor
          modulus Reference head) := by
          rw [step]
        _ = (nativeProduct (environment := environment) modulus Reference tail * j) * sourceFactor
          modulus Reference head := by
          rw [Matrix.mul_assoc]
        _ = _ := by
          rw [induction]
          simp only [Matrix.mul_assoc]
          rfl

/-- Full mixed/reference evolution of any record-conditioned actual native sequence. -/
lemma nativeProduct_mixed_reference (Reference : Register) (choices : List (Choice modulus))
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    let j := BasisEmbedding.matrix
      (BasisEmbedding.withReference (Carrier.zeroEmbedding modulus positive) Reference)
    let k := nativeProduct (environment := environment) modulus Reference choices
    k * (j * density * j.conjTranspose) * k.conjTranspose =
      j * σ modulus Reference choices density * j.conjTranspose := by
  rw [sigma_eq_product]
  exact ControlKraus.conjugation_intertwines _ _ _
    (nativeProduct_intertwines modulus positive Reference choices) density

/-- Concatenating streams feeds the complete first posterior into the second stream. -/
lemma sigma_append (Reference : Register) (first second : List (Choice modulus))
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    σ modulus Reference (first ++ second) density =
      σ modulus Reference second (σ modulus Reference first density) := by
  induction first generalizing density with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, σ, induction]

/-- Earlier measured outputs in one exponent choose the actual feedback phase angles. -/
def feedbackAngle (inverse : Bool) {bits : Nat} (record : Fin bits → Fin 2)
    (position : Fin bits) : (count : Nat) → count ≤ position.val → ℝ
  | 0, _ => 0
  | count + 1, bounded =>
      feedbackAngle inverse record position count (Nat.le_of_succ_le bounded) +
        if (record ⟨count, Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.le_succ count) bounded) position.isLt⟩).val = 1 then
          if inverse then -(QuantumFourierTransform.Source.phaseAngle (position.val - count - 1))
          else QuantumFourierTransform.Source.phaseAngle (position.val - count - 1)
        else 0

/-- Powers are addressed MSB first; records remain in the chronological LSB output order. -/
def exponentChoices (inverse : Bool) {bits : Nat} (unit : (ZMod modulus.val)ˣ)
    (record : Fin bits → Fin 2) : List (Choice modulus) :=
  List.ofFn fun position : Fin bits =>
    ⟨unit ^ (2 ^ position.rev.val), feedbackAngle inverse record position position.val le_rfl,
      record position⟩

omit [NeZero modulus.val] in
lemma exponentChoices_length (inverse : Bool) {bits : Nat}
    (unit : (ZMod modulus.val)ˣ) (record : Fin bits → Fin 2) :
    (exponentChoices modulus inverse unit record).length = bits := by
  simp only [exponentChoices, List.length_ofFn]

omit [NeZero modulus.val] in
lemma exponentChoices_empty (inverse : Bool) (unit : (ZMod modulus.val)ˣ)
    (record : Fin 0 → Fin 2) : exponentChoices modulus inverse unit record = [] := by
  simp only [exponentChoices, List.ofFn_zero]

/-- Both exponent streams reuse exactly the same unit and reference matrix coordinates. -/
def memberChoices (inverse : Bool) (m ell : Nat) (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (ell + m) → Fin 2) (second : Fin ell → Fin 2) : List (Choice modulus) :=
  exponentChoices modulus inverse generator first ++
    exponentChoices modulus inverse target⁻¹ second

omit [NeZero modulus.val] in
lemma memberChoices_length (inverse : Bool) (m ell : Nat)
    (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (ell + m) → Fin 2) (second : Fin ell → Fin 2) :
    (memberChoices modulus inverse m ell generator target first second).length = (ell + m) + ell :=
    by
  rw [memberChoices, List.length_append, exponentChoices_length, exponentChoices_length]

/-- There is no seed reload at the exponent boundary, even with entanglement to a reference. -/
lemma member_mixed_reference (inverse : Bool) (m ell : Nat)
    (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (ell + m) → Fin 2) (second : Fin ell → Fin 2) (Reference : Register)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    let j := BasisEmbedding.matrix
      (BasisEmbedding.withReference (Carrier.zeroEmbedding modulus positive) Reference)
    let k := nativeProduct (environment := environment) modulus Reference
      (memberChoices modulus inverse m ell generator target first second)
    k * (j * density * j.conjTranspose) * k.conjTranspose =
      j * σ modulus Reference (exponentChoices modulus inverse target⁻¹ second)
        (σ modulus Reference (exponentChoices modulus inverse generator first) density) *
          j.conjTranspose := by
  have whole := nativeProduct_mixed_reference (environment := environment) modulus positive
    Reference
    (memberChoices modulus inverse m ell generator target first second) density
  simpa only [memberChoices, sigma_append] using whole

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Trajectory
