/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Record
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Mixed

/-!
# Every actual exponent record on the same coherent accumulator and reference

The chronological source product reads the real preceding Store. The scalar
contains only the public arithmetic constants and positions; it is independent
of every arithmetic/readout outcome, old Store and coherent reference input.
Physical reset restores the same zero-control carrier after each stage
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ExpMatrixCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]
  (wide : 2 ≤ width) {bits : Nat} (unit : (ZMod modulus.toNat)ˣ)

/-- The common arithmetic scalar contains no chronological measurement outcomes. -/
def exponentAlpha : (remaining position : Nat) → position + remaining ≤ bits → ℂ
  | 0, _, _ => 1
  | remaining + 1, position, bounded =>
      exponentAlpha remaining (position + 1) (by omega) *
        arithmeticAlpha width modulus (unit ^ (2 ^ (⟨position, by omega⟩ : Fin bits).rev.val))

variable (inverse : Bool)
  (outputs : Fin bits → CWriteRef (ExpMatrixCtx base noQuantum m ell width) (.finite 2))

/-- Logical chronological matrices with the actual previous Store, before forgetting any record. -/
def exponentSourceKraus (Reference : Register) : (remaining position : Nat) →
    (bounded : position + remaining ≤ bits) → Store (ExpMatrixCtx base noQuantum m ell width) →
    ExponentOutcomes base noQuantum m ell width modulus wide unit remaining position bounded →
    HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference)
  | 0, _, _, _, _ => 1
  | remaining + 1, position, bounded, store, outcomes =>
      let current : Fin bits := ⟨position, by omega⟩
      let head := stageRecord base noQuantum m ell width modulus wide inverse outputs unit
        current store outcomes.1.1 outcomes.1.2
      exponentSourceKraus Reference remaining (position + 1) (by omega) head.1 outcomes.2 *
        stageSourceKraus base noQuantum m ell width modulus inverse outputs unit current Reference
          store (EncodedBit.MeasuredUncompute.placedOutcome (Physical.layout width).control
            (Physical.qubits width) (ExpMatrixCtx base noQuantum m ell width)
            (context_wires base noQuantum m ell width) outcomes.1.2)

private lemma stage_source_matrix (positive : 0 < modulus.toNat)
    (separate : ∀ vent index,
      (ventCell base noQuantum m ell width vent).key ≠ (outputs index).key)
    (position : Fin bits) (environment : model.Environment)
    (store : Store (ExpMatrixCtx base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position)
    (outcome : Fin ((ExpMatrixCtx base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) (Reference : Register) :
    stageActualKraus base noQuantum m ell width modulus wide inverse outputs unit position
        environment store measured outcome Reference *
      BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) =
    arithmeticAlpha width modulus (unit ^ (2 ^ position.rev.val)) •
      (BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) *
        stageSourceKraus base noQuantum m ell width modulus inverse outputs unit position Reference
          store (EncodedBit.MeasuredUncompute.placedOutcome (Physical.layout width).control
            (Physical.qubits width) (ExpMatrixCtx base noQuantum m ell width)
            (context_wires base noQuantum m ell width) outcome)) := by
  have action := stageActualKraus_zero_matrix base noQuantum m ell width modulus wide positive
    inverse outputs unit position environment store measured outcome Reference
  rw [stageArithmetic_feedbackScalar base noQuantum m ell width modulus wide inverse outputs
    separate unit position store measured] at action
  exact action

/-- Every original record preserves the full unit/reference carrier with one common scalar. -/
lemma exponentActualKraus_zero_matrix (positive : 0 < modulus.toNat)
    (separate : ∀ vent index,
      (ventCell base noQuantum m ell width vent).key ≠ (outputs index).key)
    (environment : model.Environment) (Reference : Register) (remaining position : Nat)
    (bounded : position + remaining ≤ bits)
    (store : Store (ExpMatrixCtx base noQuantum m ell width))
    (outcomes : ExponentOutcomes base noQuantum m ell width modulus wide unit remaining position
      bounded) :
    exponentActualKraus base noQuantum m ell width modulus wide unit inverse outputs environment
        Reference remaining position bounded store outcomes *
      BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) =
    exponentAlpha width modulus unit remaining position bounded •
      (BasisEmbedding.matrix (zeroJointEmbedding base noQuantum m ell width modulus Reference) *
        exponentSourceKraus base noQuantum m ell width modulus wide unit inverse outputs Reference
          remaining position bounded store outcomes) := by
  induction remaining generalizing position store with
  | zero => simp only [exponentActualKraus, exponentAlpha, exponentSourceKraus, Matrix.one_mul,
      Matrix.mul_one, one_smul]
  | succ remaining induction =>
      change (_ * _) * _ = _
      rw [Matrix.mul_assoc, stage_source_matrix base noQuantum m ell width modulus wide unit
        inverse outputs positive separate, Matrix.mul_smul, ← Matrix.mul_assoc,
        induction (position + 1) (by omega), Matrix.smul_mul, smul_smul]
      simp only [exponentAlpha, exponentSourceKraus, mul_comm, Matrix.mul_assoc]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
