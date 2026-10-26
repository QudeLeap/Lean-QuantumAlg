/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Feedback
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Placement.Single
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic.Instrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Feedback
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Source.Reference
import all QuantumAlg.Core.Base.Tensor.Reference
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Carrier.Reference

/-!
# Actual stored feedback matrix on the complete measured unit/reference carrier

The phase product reads the real previous output cells in the current Store.
Every factor comes from its paid native phase or literal identity. Original
Store correlations and arbitrary coherent reference entries remain explicit
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open scoped Kronecker

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- Each actual selected native phase has the independently specified full logical phase block. -/
lemma feedbackProgram_intertwines (inverse : Bool) (separation : Nat)
    (value : CShape.Value (.finite 2)) (environment : OracleModel.empty.Interpretation) :
    ((feedbackProgram base noQuantum m ell width inverse separation value).matrix environment :
        HilbertOperator (Context base noQuantum m ell width).register) *
      BasisEmbedding.matrix (Placement.embedding base noQuantum m ell width modulus) =
    BasisEmbedding.matrix (Placement.embedding base noQuantum m ell width modulus) *
      Recycling.ControlKraus.phaseBlock (S := Recycling.Carrier.units modulus.toNat)
        (Recycling.FeedbackCarrier.selectedScalar inverse separation value) := by
  cases value with
  | finite bit =>
      by_cases selected : bit.val = 1
      · simp only [feedbackProgram, CShape.Value.toFin_finite, selected, if_true,
          Recycling.FeedbackCarrier.selectedScalar, Recycling.FeedbackCarrier.selectedAngle]
        rw [← Recycling.ControlKraus.phase_matrix
          (⟨modulus.toNat, Nat.lt_succ_of_lt modulus.isLt⟩ : Fin (2 ^ width + 1))]
        exact Placement.phase_intertwines base noQuantum m ell width modulus _ environment
      · simp only [feedbackProgram, CShape.Value.toFin_finite, selected, if_false,
          Recycling.FeedbackCarrier.selectedScalar, Recycling.FeedbackCarrier.selectedAngle,
          Complex.ofReal_zero, zero_mul, Complex.exp_zero, UnitaryCircuit.identity_matrix,
          Recycling.FeedbackCarrier.phaseBlock_one, Submonoid.coe_one, Matrix.one_mul,
          Matrix.mul_one]

/-- Literal scalar product of the phases selected by the actual chronological output prefix. -/
def feedbackScalar (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) : (count : Nat) → count ≤ position.val →
      Store (Context base noQuantum m ell width) → ℂ
  | 0, _, _ => 1
  | count + 1, bounded, store =>
      Recycling.FeedbackCarrier.selectedScalar inverse (position.val - count - 1)
        (store.read (.storage
          (outputs ⟨count, by have bound := position.isLt; omega⟩).toCStorageRef)) *
        feedbackScalar inverse outputs position count (by omega) store

/-- The full actual paid feedback prefix has the exact logical phase product. -/
lemma feedbackAction_intertwines (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val)
    (environment : OracleModel.empty.Interpretation)
    (store : Store (Context base noQuantum m ell width)) :
    (feedbackAction base noQuantum m ell width environment inverse outputs position count bounded
      store : HilbertOperator (Context base noQuantum m ell width).register) *
      BasisEmbedding.matrix (Placement.embedding base noQuantum m ell width modulus) =
    BasisEmbedding.matrix (Placement.embedding base noQuantum m ell width modulus) *
      Recycling.ControlKraus.phaseBlock (S := Recycling.Carrier.units modulus.toNat)
        (feedbackScalar base noQuantum m ell width inverse outputs position count bounded store) :=
    by
  induction count with
  | zero =>
      simp only [feedbackAction, feedbackScalar, Recycling.FeedbackCarrier.phaseBlock_one,
        Submonoid.coe_one, Matrix.one_mul, Matrix.mul_one]
  | succ count induction =>
      let previous := outputs ⟨count, by have bound := position.isLt; omega⟩
      let value := store.read (.storage previous.toCStorageRef)
      let current := Recycling.FeedbackCarrier.selectedScalar inverse (position.val - count - 1)
        value
      let prior := feedbackScalar base noQuantum m ell width inverse outputs position count
        (by omega) store
      let native : HilbertOperator (Context base noQuantum m ell width).register :=
        (feedbackProgram base noQuantum m ell width inverse (position.val - count - 1)
          value).matrix environment
      let old : HilbertOperator (Context base noQuantum m ell width).register :=
        feedbackAction base noQuantum m ell width environment inverse outputs position count
          (by omega) store
      let embedding :=
        BasisEmbedding.matrix (Placement.embedding base noQuantum m ell width modulus)
      let source (scalar : ℂ) :=
        Recycling.ControlKraus.phaseBlock (S := Recycling.Carrier.units modulus.toNat) scalar
      have currentAction : native * embedding = embedding * source current :=
        feedbackProgram_intertwines base noQuantum m ell width modulus inverse
          (position.val - count - 1) value environment
      have priorAction : old * embedding = embedding * source prior := induction (by omega)
      change (native * old) * embedding = embedding * source (current * prior)
      calc
        _ = native * (old * embedding) := Matrix.mul_assoc _ _ _
        _ = native * (embedding * source prior) := by rw [priorAction]
        _ = (native * embedding) * source prior := (Matrix.mul_assoc _ _ _).symm
        _ = (embedding * source current) * source prior := by rw [currentAction]
        _ = _ := by
          rw [Matrix.mul_assoc, Recycling.FeedbackCarrier.phaseBlock_mul]

/-- The same actual feedback intertwiner retains arbitrary external-reference coherences. -/
lemma feedbackAction_reference (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val)
    (environment : OracleModel.empty.Interpretation)
    (store : Store (Context base noQuantum m ell width)) (Reference : Register) :
    (UnitaryOperator.prodTensor
      (feedbackAction base noQuantum m ell width environment inverse outputs position count bounded
        store) (1 : UnitaryOperator Reference) :
          HilbertOperator ((Context base noQuantum m ell width).register.prod Reference)) *
      BasisEmbedding.matrix
        (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) =
    BasisEmbedding.matrix
        (arithmeticJointEmbedding base noQuantum m ell width modulus Reference) *
      sourceWithReference
        (Recycling.ControlKraus.phaseBlock (S := Recycling.Carrier.units modulus.toNat)
          (feedbackScalar base noQuantum m ell width inverse outputs position count bounded store))
        Reference := by
  have derived := Recycling.NativeBranch.reference_intertwines _ _ _
    (feedbackAction_intertwines base noQuantum m ell width modulus inverse outputs position count
      bounded environment store) Reference
  simpa only [unitaryOperator_prodTensor_identity, arithmeticJointEmbedding,
    sourceWithReference_kronecker] using derived

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
