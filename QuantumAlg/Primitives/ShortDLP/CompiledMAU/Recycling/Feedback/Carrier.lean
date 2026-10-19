/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Placement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Feedback
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Native.Branch
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Trajectory
import all QuantumAlg.Components.Gates.PhaseOperator
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Actual stored feedback on the clean carrier

The scalar is computed from the actual
previous cells in the current complete Store. Every factor is the native gate
selected by that value. The full mixed/reference action therefore retains
caller correlations with old cell values, and the phase combination is proved
from the actual finite prefix rather than supplied as a certificate.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.FeedbackCarrier

noncomputable section

open Execution

variable {environment : model.Environment}
open scoped Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma phaseBlock_one {S : Register} :
    ControlKraus.phaseBlock (S := S) 1 = 1 := by
  let block : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) ℂ :=
    ControlKraus.phaseBlock (S := S) 1
  change block = (1 : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) ℂ)
  ext row column
  by_cases bit : row.1 = column.1 <;> by_cases seed : row.2 = column.2 <;>
    simp [block, ControlKraus.phaseBlock, Matrix.one_apply, Prod.ext_iff, bit, seed]

private lemma phaseBlock_mul {S : Register} (left right : ℂ) :
    ControlKraus.phaseBlock (S := S) left * ControlKraus.phaseBlock right =
      ControlKraus.phaseBlock (left * right) := by
  let block (phase : ℂ) : Matrix (Fin 2 × S.Index) (Fin 2 × S.Index) ℂ :=
    ControlKraus.phaseBlock (S := S) phase
  have diagonal (phase : ℂ) : block phase =
      Matrix.diagonal (fun entry : Fin 2 × S.Index => if entry.1 = 0 then 1 else phase) := by
    ext row column
    by_cases bit : row.1 = column.1 <;> by_cases seed : row.2 = column.2 <;>
      simp [block, ControlKraus.phaseBlock, Matrix.diagonal_apply, Matrix.one_apply,
        Prod.ext_iff, bit, seed]
  change block left * block right = block (left * right)
  rw [diagonal, diagonal, diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext entry
  by_cases zero : entry.1 = 0 <;> simp [zero]

def selectedAngle (inverse : Bool) (separation : Nat) (value : CShape.Value (.finite 2)) : ℝ :=
  match value with
  | .finite bit => if bit.val = 1 then
      if inverse then -(QuantumFourierTransform.Source.phaseAngle separation)
      else QuantumFourierTransform.Source.phaseAngle separation
    else 0

def selectedScalar (inverse : Bool) (separation : Nat)
    (value : CShape.Value (.finite 2)) : ℂ :=
  Complex.exp ((selectedAngle inverse separation value : ℂ) * Complex.I)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val] (positive : 0 < modulus.val)

/-- Each actual previous-value-selected native gate supplies its own full intertwiner. -/
lemma feedbackProgram_intertwines (inverse : Bool) (separation : Nat)
    (value : CShape.Value (.finite 2)) :
    (((feedbackProgram base noQuantum m ell width inverse separation value).matrix
      environment.quantum) :
        HilbertOperator (Context base noQuantum m ell width).register) *
      BasisEmbedding.matrix (Placement.embedding base noQuantum m ell width modulus positive) =
    BasisEmbedding.matrix (Placement.embedding base noQuantum m ell width modulus positive) *
      ControlKraus.phaseBlock (S := Carrier.units modulus.val)
        (selectedScalar inverse separation value) := by
  cases value with
  | finite bit =>
    by_cases selected : bit.val = 1
    · simp only [feedbackProgram, selected, if_true, selectedScalar, selectedAngle]
      rw [← ControlKraus.phase_matrix modulus]
      exact Placement.single_intertwines base noQuantum m ell width modulus positive _
    · simp only [feedbackProgram, selected, if_false, selectedScalar, selectedAngle,
        Complex.ofReal_zero, zero_mul, Complex.exp_zero, UnitaryCircuit.identity_matrix,
        phaseBlock_one, Submonoid.coe_one, Matrix.one_mul, Matrix.mul_one]

/-- This is the literal product of phases selected by the actual stored earlier outputs. -/
def scalar (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) : (count : Nat) → count ≤ position.val →
      Store (Context base noQuantum m ell width) → ℂ
  | 0, _, _ => 1
  | count + 1, bounded, store =>
      selectedScalar inverse (position.val - count - 1)
        (store.read (.storage ((outputs ⟨count, Nat.lt_of_le_of_lt
          (Nat.le_trans (Nat.le_succ count) bounded) position.isLt⟩).toCStorageRef))) *
        scalar inverse outputs position count (Nat.le_of_succ_le bounded) store

/-- The exact prefix angle is a sum only over earlier cells of this exponent. -/
def angle (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) : (count : Nat) → count ≤ position.val →
      Store (Context base noQuantum m ell width) → ℝ
  | 0, _, _ => 0
  | count + 1, bounded, store =>
      angle inverse outputs position count (Nat.le_of_succ_le bounded) store +
        selectedAngle inverse (position.val - count - 1)
          (store.read (.storage ((outputs ⟨count, Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.le_succ count) bounded) position.isLt⟩).toCStorageRef)))

lemma scalar_eq_exp (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val)
    (store : Store (Context base noQuantum m ell width)) :
    scalar base noQuantum m ell width inverse outputs position count bounded store =
      Complex.exp ((angle base noQuantum m ell width inverse outputs position count bounded
        store : ℂ) * Complex.I) := by
  induction count with
  | zero => simp only [scalar, angle, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  | succ count induction =>
      rw [scalar, induction, angle, selectedScalar, ← Complex.exp_add]
      congr 1
      push_cast
      ring

def storedRecord {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (store : Store (Context base noQuantum m ell width)) : Fin bits → Fin 2 :=
  fun position => (store.read (.storage (outputs position).toCStorageRef)).toFin

lemma angle_eq_record (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (count : Nat) (bounded : count ≤ position.val)
    (store : Store (Context base noQuantum m ell width)) :
    angle base noQuantum m ell width inverse outputs position count bounded store =
      Trajectory.feedbackAngle inverse
        (storedRecord base noQuantum m ell width outputs store) position count bounded := by
  induction count with
  | zero => rfl
  | succ count induction =>
      rw [angle, Trajectory.feedbackAngle, induction]
      congr 1
      dsimp only [storedRecord]
      have selectedValue (value : CShape.Value (.finite 2)) :
          selectedAngle inverse (position.val - count - 1) value =
            if value.toFin.val = 1 then
              if inverse then -(QuantumFourierTransform.Source.phaseAngle
                (position.val - count - 1))
              else QuantumFourierTransform.Source.phaseAngle (position.val - count - 1)
            else 0 := by
        cases value with
        | finite bit => rfl
      exact selectedValue _

/-- Complete native feedback action beside an arbitrary unchanged reference. -/
lemma feedbackAction_intertwines (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (Reference : Register) (count : Nat) (bounded : count ≤ position.val)
    (store : Store (Context base noQuantum m ell width)) :
    let nativeRef : Matrix ((Context base noQuantum m ell width).register.prod Reference).Index
        ((Context base noQuantum m ell width).register.prod Reference).Index ℂ :=
      feedbackAction (environment := environment) base noQuantum m ell width inverse outputs
        position Reference count bounded
        store
    let sourceRef : Matrix ((Carrier.full modulus.val).prod Reference).Index
        ((Carrier.full modulus.val).prod Reference).Index ℂ :=
      ControlKraus.phaseBlock (S := Carrier.units modulus.val)
        (scalar base noQuantum m ell width inverse outputs position count bounded store) ⊗ₖ
          (1 : HilbertOperator Reference)
    let j : Matrix ((Context base noQuantum m ell width).register.prod Reference).Index
        ((Carrier.full modulus.val).prod Reference).Index ℂ :=
      BasisEmbedding.matrix (BasisEmbedding.withReference
        (Placement.embedding base noQuantum m ell width modulus positive) Reference)
    nativeRef * j = j * sourceRef := by
  dsimp only
  let j : Matrix ((Context base noQuantum m ell width).register.prod Reference).Index
      ((Carrier.full modulus.val).prod Reference).Index ℂ :=
    BasisEmbedding.matrix (BasisEmbedding.withReference
      (Placement.embedding base noQuantum m ell width modulus positive) Reference)
  let source (phase : ℂ) : Matrix ((Carrier.full modulus.val).prod Reference).Index
      ((Carrier.full modulus.val).prod Reference).Index ℂ :=
    ControlKraus.phaseBlock (S := Carrier.units modulus.val) phase ⊗ₖ
      (1 : HilbertOperator Reference)
  induction count with
  | zero =>
      simp only [feedbackAction, scalar, phaseBlock_one, Matrix.one_kronecker_one,
        Submonoid.coe_one, Matrix.one_mul, Matrix.mul_one]
  | succ count induction =>
      let previous := outputs ⟨count, Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.le_succ count) bounded) position.isLt⟩
      let value := store.read (.storage previous.toCStorageRef)
      let current := selectedScalar inverse (position.val - count - 1) value
      let prior := scalar base noQuantum m ell width inverse outputs position count
        (Nat.le_of_succ_le bounded) store
      let native : Matrix ((Context base noQuantum m ell width).register.prod Reference).Index
          ((Context base noQuantum m ell width).register.prod Reference).Index ℂ :=
        UnitaryOperator.prodTensor
          ((feedbackProgram base noQuantum m ell width inverse (position.val - count - 1)
            value).matrix environment.quantum) (1 : UnitaryOperator Reference)
      have currentIntertwines : native * j = j * source current := by
        have derived := NativeBranch.reference_intertwines _ _ _
          (feedbackProgram_intertwines (environment := environment) base noQuantum m ell width
            modulus positive inverse
            (position.val - count - 1) value) Reference
        simpa only [native, j, source, current, BasisEmbedding.reference_operator] using derived
      have combine : source current * source prior = source (current * prior) := by
        dsimp only [source]
        rw [← Matrix.mul_kronecker_mul, phaseBlock_mul, Matrix.one_mul]
      let priorNative : Matrix ((Context base noQuantum m ell width).register.prod Reference).Index
          ((Context base noQuantum m ell width).register.prod Reference).Index ℂ :=
        feedbackAction (environment := environment) base noQuantum m ell width inverse outputs
          position Reference count
          (Nat.le_of_succ_le bounded) store
      have priorIntertwines : priorNative * j = j * source prior :=
        induction (Nat.le_of_succ_le bounded)
      change (native * priorNative) * j = j * source (current * prior)
      calc
        (native * priorNative) * j = native * (priorNative * j) := Matrix.mul_assoc _ _ _
        _ = native * (j * source prior) := by rw [priorIntertwines]
        _ = (native * j) * source prior := by rw [Matrix.mul_assoc]
        _ = _ := by rw [currentIntertwines, Matrix.mul_assoc, combine]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.FeedbackCarrier
