/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.ControlKraus
import all QuantumAlg.Components.QuditShift.Qubit
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Measure.Instrument
import all QuantumAlg.Components.Encoded.StateEmbedding
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Actual native measurement/correction on the persistent clean carrier

The branch below contains the native
H/arithmetic/phase/H prefix, the projector of the actual first wire, and the
actual identity/X correction used by measured reset. Its complete rectangular
intertwiner is derived from those programs. Arbitrary mixed matrices and an
unchanged reference are retained; neither a channel equation nor an input
certificate is assumed. Store-selected feedback and context placement remain
separate integration steps in the actual executable member.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.NativeBranch

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open scoped Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {width : Nat} (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]
  (positive : 0 < modulus.val)

private abbrev nativeLayout (width : Nat) := (Arithmetic.layout width).toQuantum

private abbrev nativeControl (width : Nat) : Fin (1 + (workspaceEncoding width).width) := 0

/-- This is the actual identity/X program selected by the newly measured outcome. -/
def correction (outcome : Fin 2) :
    UnitaryCircuit AlgorithmGate.model .empty (nativeLayout width) :=
  QuditShift.qubitShiftCircuit (nativeLayout width) (nativeControl width) rfl .empty (-outcome)

def sourceCorrection (outcome : Fin 2) : UnitaryOperator (Carrier.full modulus.val) :=
  UnitaryOperator.prodTensor (if outcome = 0 then 1 else Gate.XOp)
    (1 : UnitaryOperator (Carrier.units modulus.val))

/-- The actual measured-control projector, before its real identity/X correction. -/
def projector (outcome : Fin 2) : HilbertOperator (Carrier.physical width) :=
  ZMeasurement.projector (fun basis => basis (nativeControl width)) outcome

def sourceProjector (outcome : Fin 2) : HilbertOperator (Carrier.full modulus.val) :=
  ZMeasurement.projector Prod.fst outcome

private lemma prodTensor_identity (Left Right : Register) :
    UnitaryOperator.prodTensor (1 : UnitaryOperator Left) (1 : UnitaryOperator Right) = 1 := by
  apply Subtype.ext
  change Matrix.reindex (Register.prodIndexEquiv Left Right)
    (Register.prodIndexEquiv Left Right)
      ((1 : HilbertOperator Left) ⊗ₖ (1 : HilbertOperator Right)) = _
  rw [Matrix.one_kronecker_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  rfl

/-- Actual outcome-selected corrections supply their own clean carrier intertwiner. -/
lemma correction_intertwines (outcome : Fin 2) :
    (((correction (width := width) outcome).matrix environment) : HilbertOperator (Carrier.physical
      width)) *
        BasisEmbedding.matrix (Carrier.embedding modulus positive) =
      BasisEmbedding.matrix (Carrier.embedding modulus positive) *
        (sourceCorrection modulus outcome : HilbertOperator (Carrier.full modulus.val)) := by
  have correctionZero : correction (width := width) (0 : Fin 2) =
      UnitaryCircuit.identity AlgorithmGate.model .empty (nativeLayout width) := by
    unfold correction QuditShift.qubitShiftCircuit
    exact if_pos (show -(0 : Fin 2) = 0 by decide)
  have correctionOne : correction (width := width) (1 : Fin 2) =
      Carrier.oneQubit (width := width) Gate.XOp := by
    unfold correction QuditShift.qubitShiftCircuit Carrier.oneQubit
    exact if_neg (show -(1 : Fin 2) ≠ 0 by decide)
  have sourceZero : sourceCorrection modulus (0 : Fin 2) = 1 := by
    unfold sourceCorrection
    rw [if_pos rfl, prodTensor_identity]
  have sourceOne : sourceCorrection modulus (1 : Fin 2) =
      UnitaryOperator.prodTensor Gate.XOp (1 : UnitaryOperator (Carrier.units modulus.val)) := by
    unfold sourceCorrection
    exact congrArg (fun gate => UnitaryOperator.prodTensor gate
      (1 : UnitaryOperator (Carrier.units modulus.val))) (if_neg (by decide))
  fin_cases outcome
  · change (((correction (width := width) (0 : Fin 2)).matrix environment) :
        HilbertOperator (Carrier.physical width)) *
        BasisEmbedding.matrix (Carrier.embedding modulus positive) =
      BasisEmbedding.matrix (Carrier.embedding modulus positive) *
        (sourceCorrection modulus (0 : Fin 2) : HilbertOperator (Carrier.full modulus.val))
    rw [correctionZero, UnitaryCircuit.identity_matrix, sourceZero]
    simp only [Submonoid.coe_one, Matrix.one_mul, Matrix.mul_one]
  · change (((correction (width := width) (1 : Fin 2)).matrix environment) :
        HilbertOperator (Carrier.physical width)) *
        BasisEmbedding.matrix (Carrier.embedding modulus positive) =
      BasisEmbedding.matrix (Carrier.embedding modulus positive) *
        (sourceCorrection modulus (1 : Fin 2) : HilbertOperator (Carrier.full modulus.val))
    rw [correctionOne, sourceOne]
    exact Carrier.oneQubit_intertwines modulus positive Gate.XOp

/-- Measuring the actual wire selects exactly the corresponding logical control fiber. -/
lemma projector_intertwines (outcome : Fin 2) :
    projector (width := width) outcome *
        BasisEmbedding.matrix (Carrier.embedding modulus positive) =
      BasisEmbedding.matrix (Carrier.embedding modulus positive) *
        sourceProjector modulus outcome := by
  ext row column
  simp only [projector, sourceProjector, ZMeasurement.projector,
    Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases encoded : Carrier.embedding modulus positive column = row
  · subst row
    have control : Carrier.embedding modulus positive column (nativeControl width) =
        column.1 := Carrier.embedding_control modulus positive column
    simp only [BasisEmbedding.matrix, if_true, mul_one, one_mul]
    exact congrArg (fun bit : Fin 2 => if bit = outcome then (1 : ℂ) else 0) control
  · simp only [BasisEmbedding.matrix, encoded, if_false, mul_zero, zero_mul]

/-- The logical measurement followed by its actual correction is the reset partial isometry. -/
lemma source_reset_matrix (outcome : Fin 2) :
    (sourceCorrection modulus outcome : HilbertOperator (Carrier.full modulus.val)) *
        sourceProjector modulus outcome = ControlKraus.resetBlock outcome := by
  ext row column
  simp only [sourceProjector, ZMeasurement.projector, Matrix.mul_diagonal]
  simp only [sourceCorrection, UnitaryOperator.unitaryOperator_prodTensor_apply]
  rcases row with ⟨rowBit, rowSeed⟩
  rcases column with ⟨columnBit, columnSeed⟩
  fin_cases outcome <;> fin_cases rowBit <;> fin_cases columnBit <;>
    simp [ControlKraus.resetBlock, Gate.XOp, UnitaryOperator.ofPerm_entry,
      Matrix.one_apply]

/-- The actual matrix of a record-conditioned H/arithmetic/phase/H/measure/reset branch. -/
def operator (coefficient : (ZMod modulus.val)ˣ) (angle : ℝ) (outcome : Fin 2) :
    HilbertOperator (Carrier.physical width) :=
  (((correction (width := width) outcome).matrix environment) : HilbertOperator (Carrier.physical
    width)) *
    projector outcome *
      (((ControlKraus.nativePreparation modulus coefficient angle).matrix environment) :
        HilbertOperator (Carrier.physical width))

/-- All physical input columns of the clean control/unit carrier are accounted for. -/
lemma operator_full_intertwines (coefficient : (ZMod modulus.val)ˣ)
    (angle : ℝ) (outcome : Fin 2) :
    operator (environment := environment) modulus coefficient angle outcome *
        BasisEmbedding.matrix (Carrier.embedding modulus positive) =
      BasisEmbedding.matrix (Carrier.embedding modulus positive) *
        ControlKraus.branch (Carrier.translation modulus coefficient :
          HilbertOperator (Carrier.units modulus.val))
          (Complex.exp ((angle : ℂ) * Complex.I)) outcome := by
  let j : Matrix (Carrier.physical width).Index (Carrier.full modulus.val).Index ℂ :=
    BasisEmbedding.matrix (Carrier.embedding modulus positive)
  let u : Matrix (Carrier.physical width).Index (Carrier.physical width).Index ℂ :=
    ((ControlKraus.nativePreparation modulus coefficient angle).matrix environment)
  let v : Matrix (Carrier.full modulus.val).Index (Carrier.full modulus.val).Index ℂ :=
    ControlKraus.sourcePreparation modulus coefficient angle
  let c : Matrix (Carrier.physical width).Index (Carrier.physical width).Index ℂ :=
    ((correction (width := width) outcome).matrix environment)
  let d : Matrix (Carrier.full modulus.val).Index (Carrier.full modulus.val).Index ℂ :=
    sourceCorrection modulus outcome
  let p : Matrix (Carrier.physical width).Index (Carrier.physical width).Index ℂ :=
    projector outcome
  let q : Matrix (Carrier.full modulus.val).Index (Carrier.full modulus.val).Index ℂ :=
    sourceProjector modulus outcome
  have prepared : u * j = j * v :=
    ControlKraus.nativePreparation_intertwines modulus positive coefficient angle
  have selected : p * j = j * q := projector_intertwines modulus positive outcome
  have corrected : c * j = j * d := correction_intertwines modulus positive outcome
  have composed : (c * p * u) * j = j * (d * q * v) := by
    calc
      _ = c * (p * (u * j)) := by simp only [Matrix.mul_assoc]
      _ = c * (p * (j * v)) := by rw [prepared]
      _ = c * ((p * j) * v) := by simp only [Matrix.mul_assoc]
      _ = c * ((j * q) * v) := by rw [selected]
      _ = (c * j) * (q * v) := by simp only [Matrix.mul_assoc]
      _ = (j * d) * (q * v) := by rw [corrected]
      _ = _ := by simp only [Matrix.mul_assoc]
  change (c * p * u) * j = j * _
  refine composed.trans ?_
  change j * ((sourceCorrection modulus outcome : HilbertOperator (Carrier.full modulus.val)) *
      sourceProjector modulus outcome *
      (ControlKraus.sourcePreparation modulus coefficient angle :
        HilbertOperator (Carrier.full modulus.val))) = j * _
  rw [source_reset_matrix]
  simp only [ControlKraus.sourcePreparation, Submonoid.coe_mul, ControlKraus.branch,
    ← ControlKraus.controlledAction_matrix modulus coefficient,
    ← ControlKraus.phase_matrix modulus angle, Matrix.mul_assoc]

private lemma zero_embedding_matrix :
    BasisEmbedding.matrix (Carrier.zeroEmbedding modulus positive) =
      BasisEmbedding.matrix (Carrier.embedding modulus positive) *
        BasisEmbedding.matrix (ControlKraus.zeroInjection (S := Carrier.units modulus.val)) := by
  ext row column
  simp [Carrier.zeroEmbedding, ControlKraus.zeroInjection, BasisEmbedding.matrix,
    Matrix.mul_apply, Function.Embedding.trans_apply, mul_ite]

/-- The actual native branch induces the half-sum on the same persistent unit accumulator. -/
lemma operator_zero_intertwines (coefficient : (ZMod modulus.val)ˣ)
    (angle : ℝ) (outcome : Fin 2) :
    operator (environment := environment) modulus coefficient angle outcome *
        BasisEmbedding.matrix (Carrier.zeroEmbedding modulus positive) =
      BasisEmbedding.matrix (Carrier.zeroEmbedding modulus positive) *
        ControlKraus.halfSum (Carrier.translation modulus coefficient :
          HilbertOperator (Carrier.units modulus.val))
          (Complex.exp ((angle : ℂ) * Complex.I)) outcome := by
  rw [zero_embedding_matrix, ← Matrix.mul_assoc, operator_full_intertwines]
  rw [Matrix.mul_assoc, ControlKraus.branch_intertwines]
  simp only [Matrix.mul_assoc]

/-- Reference extension also applies to nonunitary, unnormalized Kraus branches. -/
private lemma reference_intertwines {R S : Register} (embedding : S.Index ↪ R.Index)
    (native : HilbertOperator R) (source : HilbertOperator S)
    (derived : native * BasisEmbedding.matrix embedding = BasisEmbedding.matrix embedding * source)
    (Reference : Register) :
    let nativeRef : Matrix (R.prod Reference).Index (R.prod Reference).Index ℂ :=
      native ⊗ₖ (1 : HilbertOperator Reference)
    let sourceRef : Matrix (S.prod Reference).Index (S.prod Reference).Index ℂ :=
      source ⊗ₖ (1 : HilbertOperator Reference)
    let j : Matrix (R.prod Reference).Index (S.prod Reference).Index ℂ :=
      BasisEmbedding.matrix (BasisEmbedding.withReference embedding Reference)
    nativeRef * j = j * sourceRef := by
  dsimp only
  rw [BasisEmbedding.reference_matrix (R := R) (S := S) embedding Reference,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, derived]

/-- No reference coherence is discarded by the actual control reuse. -/
lemma operator_zero_intertwines_reference (coefficient : (ZMod modulus.val)ˣ)
    (angle : ℝ) (outcome : Fin 2) (Reference : Register) :
    let nativeRef : Matrix ((Carrier.physical width).prod Reference).Index
        ((Carrier.physical width).prod Reference).Index ℂ :=
      operator (environment := environment) modulus coefficient angle outcome ⊗ₖ (1 :
        HilbertOperator Reference)
    let sourceRef : Matrix ((Carrier.units modulus.val).prod Reference).Index
        ((Carrier.units modulus.val).prod Reference).Index ℂ :=
      ControlKraus.halfSum (Carrier.translation modulus coefficient :
        HilbertOperator (Carrier.units modulus.val))
          (Complex.exp ((angle : ℂ) * Complex.I)) outcome ⊗ₖ (1 : HilbertOperator Reference)
    let j : Matrix ((Carrier.physical width).prod Reference).Index
        ((Carrier.units modulus.val).prod Reference).Index ℂ :=
      BasisEmbedding.matrix
        (BasisEmbedding.withReference (Carrier.zeroEmbedding modulus positive) Reference)
    nativeRef * j = j * sourceRef :=
  reference_intertwines _ _ _
    (operator_zero_intertwines modulus positive coefficient angle outcome) Reference

/-- The complete unnormalized mixed accumulator/reference block is preserved exactly. -/
lemma operator_mixed_reference (coefficient : (ZMod modulus.val)ˣ)
    (angle : ℝ) (outcome : Fin 2) (Reference : Register)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    let j : Matrix ((Carrier.physical width).prod Reference).Index
        ((Carrier.units modulus.val).prod Reference).Index ℂ := BasisEmbedding.matrix
      (BasisEmbedding.withReference (Carrier.zeroEmbedding modulus positive) Reference)
    let k : Matrix ((Carrier.physical width).prod Reference).Index
        ((Carrier.physical width).prod Reference).Index ℂ :=
      operator (environment := environment) modulus coefficient angle outcome ⊗ₖ (1 :
        HilbertOperator Reference)
    let b : Matrix ((Carrier.units modulus.val).prod Reference).Index
        ((Carrier.units modulus.val).prod Reference).Index ℂ :=
      ControlKraus.halfSum (Carrier.translation modulus coefficient :
        HilbertOperator (Carrier.units modulus.val))
          (Complex.exp ((angle : ℂ) * Complex.I)) outcome ⊗ₖ (1 : HilbertOperator Reference)
    k * (j * density * j.conjTranspose) * k.conjTranspose =
      j * (b * density * b.conjTranspose) * j.conjTranspose := by
  exact ControlKraus.conjugation_intertwines _ _ _
    (operator_zero_intertwines_reference modulus positive coefficient angle outcome Reference)
    density

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.NativeBranch
