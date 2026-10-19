/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context.Reset
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Feedback.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Preparation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Native.Branch
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Components.Encoded.StateEmbedding
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Actual stored clean-carrier stage instrument

The internally encoded source state may
correlate arbitrary mixed unit/reference blocks with any caller Store and
prior history. The actual stage derives its branch half-sum from native gates,
stored feedback and measured reset. No matrix or instrument certificate is an
input. Encoding is only a mathematical comparison; it is not a free gate,
packing operation, or new cleanliness premise of the public factoring problem.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.CleanStage

noncomputable section

open Execution

variable {environment : model.Environment}
open scoped Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val] (positive : 0 < modulus.val)

private def jointEmbedding (Reference : Register) :=
  BasisEmbedding.withReference
    (Placement.embedding base noQuantum m ell width modulus positive) Reference

def zeroEmbedding (Reference : Register) :=
  BasisEmbedding.withReference
    (Placement.zeroEmbedding base noQuantum m ell width modulus positive) Reference

def sourcePreparation (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.val)ˣ) (position : Fin bits)
    (store : Store (Context base noQuantum m ell width)) :
    HilbertOperator (Carrier.full modulus.val) :=
  (ControlKraus.hadamard (S := Carrier.units modulus.val) :
    HilbertOperator (Carrier.full modulus.val)) *
    ControlKraus.phaseBlock
      (FeedbackCarrier.scalar base noQuantum m ell width inverse outputs position
        position.val le_rfl store) *
    ControlKraus.controlledBlock (Carrier.translation modulus (unit ^ (2 ^ position.rev.val)) :
      HilbertOperator (Carrier.units modulus.val)) *
    (ControlKraus.hadamard (S := Carrier.units modulus.val) :
    HilbertOperator (Carrier.full modulus.val))

/-- The full actual stored-feedback prefix derives its exact source/reference operator. -/
lemma preparationAction_intertwines (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.val)ˣ) (position : Fin bits) (Reference : Register)
    (store : Store (Context base noQuantum m ell width)) :
    let nativeRef : Matrix ((Context base noQuantum m ell width).register.prod Reference).Index
        ((Context base noQuantum m ell width).register.prod Reference).Index ℂ :=
      preparationAction (environment := environment) base noQuantum m ell width inverse outputs
        modulus.val unit position
        Reference store
    let sourceRef : Matrix ((Carrier.full modulus.val).prod Reference).Index
        ((Carrier.full modulus.val).prod Reference).Index ℂ :=
      sourcePreparation base noQuantum m ell width modulus inverse outputs unit position store ⊗ₖ
        (1 : HilbertOperator Reference)
    let j : Matrix ((Context base noQuantum m ell width).register.prod Reference).Index
        ((Carrier.full modulus.val).prod Reference).Index ℂ :=
      BasisEmbedding.matrix
        (jointEmbedding base noQuantum m ell width modulus positive Reference)
    nativeRef * j = j * sourceRef := by
  dsimp only
  let j : Matrix ((Context base noQuantum m ell width).register.Index × Reference.Index)
      ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index) ℂ :=
    BasisEmbedding.matrix
      (jointEmbedding base noQuantum m ell width modulus positive Reference)
  let hNative : Matrix ((Context base noQuantum m ell width).register.Index × Reference.Index)
      ((Context base noQuantum m ell width).register.Index × Reference.Index) ℂ :=
    (UnitaryOperator.prodTensor ((single base noQuantum m ell width Gate.HOp).matrix
      environment.quantum)
      (1 : UnitaryOperator Reference) :
        HilbertOperator ((Context base noQuantum m ell width).register.prod Reference))
  let cNative : Matrix ((Context base noQuantum m ell width).register.Index × Reference.Index)
      ((Context base noQuantum m ell width).register.Index × Reference.Index) ℂ :=
    (UnitaryOperator.prodTensor
      ((arithmetic base noQuantum m ell width modulus.val (unit ^ (2 ^ position.rev.val))).matrix
        environment.quantum)
        (1 : UnitaryOperator Reference) :
          HilbertOperator ((Context base noQuantum m ell width).register.prod Reference))
  let fNative : Matrix ((Context base noQuantum m ell width).register.Index × Reference.Index)
      ((Context base noQuantum m ell width).register.Index × Reference.Index) ℂ :=
    (feedbackAction (environment := environment) base noQuantum m ell width inverse outputs
      position Reference position.val
      le_rfl store : HilbertOperator
        ((Context base noQuantum m ell width).register.prod Reference))
  let hSource : Matrix ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index)
      ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index) ℂ :=
    (ControlKraus.hadamard (S := Carrier.units modulus.val) :
      HilbertOperator (Carrier.full modulus.val)) ⊗ₖ (1 : HilbertOperator Reference)
  let cSource : Matrix ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index)
      ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index) ℂ :=
    ControlKraus.controlledBlock
      (Carrier.translation modulus (unit ^ (2 ^ position.rev.val)) :
        HilbertOperator (Carrier.units modulus.val)) ⊗ₖ (1 : HilbertOperator Reference)
  let fSource : Matrix ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index)
      ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index) ℂ :=
    ControlKraus.phaseBlock (S := Carrier.units modulus.val)
      (FeedbackCarrier.scalar base noQuantum m ell width inverse outputs position position.val
        le_rfl store) ⊗ₖ (1 : HilbertOperator Reference)
  have h : hNative * j = j * hSource := by
    have actual := NativeBranch.reference_intertwines _ _ _
      (Placement.single_intertwines (environment := environment.quantum) base noQuantum m ell width
        modulus positive Gate.HOp) Reference
    simpa only [hNative, hSource, j, jointEmbedding, ControlKraus.hadamard,
      BasisEmbedding.reference_operator] using actual
  have c : cNative * j = j * cSource := by
    have actual := NativeBranch.reference_intertwines _ _ _
      (Placement.arithmetic_intertwines (environment := environment.quantum) base noQuantum m ell
        width modulus positive
        (unit ^ (2 ^ position.rev.val))) Reference
    simpa only [cNative, cSource, j, jointEmbedding, BasisEmbedding.reference_operator,
      ControlKraus.controlledAction_matrix] using actual
  have f : fNative * j = j * fSource := by
    have actual := FeedbackCarrier.feedbackAction_intertwines (environment := environment) base
      noQuantum m ell width modulus
      positive inverse outputs position Reference position.val le_rfl store
    simpa only [fNative, fSource, j, jointEmbedding] using actual
  have composed : (((hNative * fNative) * cNative) * hNative) * j =
      j * (((hSource * fSource) * cSource) * hSource) := by
    calc
      _ = hNative * (fNative * (cNative * (hNative * j))) := by
        simp only [Matrix.mul_assoc]
      _ = hNative * (fNative * (cNative * (j * hSource))) := by rw [h]
      _ = hNative * (fNative * ((cNative * j) * hSource)) := by
        simp only [Matrix.mul_assoc]
      _ = hNative * (fNative * ((j * cSource) * hSource)) := by rw [c]
      _ = hNative * ((fNative * j) * (cSource * hSource)) := by
        simp only [Matrix.mul_assoc]
      _ = hNative * ((j * fSource) * (cSource * hSource)) := by rw [f]
      _ = (hNative * j) * (fSource * (cSource * hSource)) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [h]; simp only [Matrix.mul_assoc]
  refine composed.trans ?_
  simp only [j, hSource, cSource, fSource, sourcePreparation]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul]

def sourceBranch (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.val)ˣ) (position : Fin bits) (Reference : Register)
    (store : Store (Context base noQuantum m ell width)) (outcome : Fin 2) :
    HilbertOperator ((Carrier.units modulus.val).prod Reference) :=
  ControlKraus.halfSum (Carrier.translation modulus (unit ^ (2 ^ position.rev.val)) :
    HilbertOperator (Carrier.units modulus.val))
      (FeedbackCarrier.scalar base noQuantum m ell width inverse outputs position position.val
        le_rfl store) outcome ⊗ₖ (1 : HilbertOperator Reference)

private lemma embedding_trans_matrix {R S T : Register}
    (first : S.Index ↪ R.Index) (second : R.Index ↪ T.Index) :
    BasisEmbedding.matrix (first.trans second) =
      BasisEmbedding.matrix second * BasisEmbedding.matrix first := by
  ext row column
  simp [Matrix.mul_apply, BasisEmbedding.matrix, Function.Embedding.trans_apply, mul_ite]

private lemma zero_embedding_matrix (Reference : Register) :
    BasisEmbedding.matrix (zeroEmbedding base noQuantum m ell width modulus positive Reference) =
      BasisEmbedding.matrix (jointEmbedding base noQuantum m ell width modulus positive Reference) *
        BasisEmbedding.matrix (BasisEmbedding.withReference
          (ControlKraus.zeroInjection (S := Carrier.units modulus.val)) Reference) := by
  have injections : zeroEmbedding base noQuantum m ell width modulus positive Reference =
      (BasisEmbedding.withReference (ControlKraus.zeroInjection (S := Carrier.units modulus.val))
        Reference).trans (jointEmbedding base noQuantum m ell width modulus positive Reference) :=
    by
    rfl
  rw [injections, embedding_trans_matrix]

/-- The literal actual stage, with actual stored feedback, derives the half-sum branch. -/
lemma stageKraus_intertwines (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.val)ˣ) (position : Fin bits) (Reference : Register)
    (store : Store (Context base noQuantum m ell width)) (outcome : Fin 2) :
    stageKraus (environment := environment) base noQuantum m ell width inverse outputs modulus.val
      unit position Reference store
        (ContextCoordinates.physicalBit base noQuantum m ell width outcome) *
      BasisEmbedding.matrix (zeroEmbedding base noQuantum m ell width modulus positive Reference) =
    BasisEmbedding.matrix (zeroEmbedding base noQuantum m ell width modulus positive Reference) *
      sourceBranch base noQuantum m ell width modulus inverse outputs unit position Reference store
        outcome := by
  let full : Matrix ((Context base noQuantum m ell width).register.Index × Reference.Index)
      ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index) ℂ :=
    BasisEmbedding.matrix
      (jointEmbedding base noQuantum m ell width modulus positive Reference)
  let zero : Matrix ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index)
      ((Carrier.units modulus.val).Index × Reference.Index) ℂ :=
    BasisEmbedding.matrix (BasisEmbedding.withReference
      (ControlKraus.zeroInjection (S := Carrier.units modulus.val)) Reference)
  let phase := FeedbackCarrier.scalar base noQuantum m ell width inverse outputs position
    position.val le_rfl store
  let translation : HilbertOperator (Carrier.units modulus.val) :=
    Carrier.translation modulus (unit ^ (2 ^ position.rev.val))
  let native : Matrix ((Context base noQuantum m ell width).register.Index × Reference.Index)
      ((Context base noQuantum m ell width).register.Index × Reference.Index) ℂ :=
    (preparationAction (environment := environment) base noQuantum m ell width inverse outputs
      modulus.val unit position
      Reference store : HilbertOperator
        ((Context base noQuantum m ell width).register.prod Reference))
  let source : Matrix ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index)
      ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index) ℂ :=
    sourcePreparation base noQuantum m ell width modulus inverse outputs unit position store ⊗ₖ
      (1 : HilbertOperator Reference)
  let resetNative : Matrix ((Context base noQuantum m ell width).register.Index × Reference.Index)
      ((Context base noQuantum m ell width).register.Index × Reference.Index) ℂ :=
    resetRow base noQuantum m ell width Reference
      (ContextCoordinates.physicalBit base noQuantum m ell width outcome)
  let resetSource : Matrix ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index)
      ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index) ℂ :=
    ControlKraus.resetBlock (S := Carrier.units modulus.val) outcome ⊗ₖ
      (1 : HilbertOperator Reference)
  let branchSource : Matrix ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index)
      ((Fin 2 × (Carrier.units modulus.val).Index) × Reference.Index) ℂ :=
    ControlKraus.branch translation phase outcome ⊗ₖ (1 : HilbertOperator Reference)
  let result : Matrix ((Carrier.units modulus.val).Index × Reference.Index)
      ((Carrier.units modulus.val).Index × Reference.Index) ℂ :=
    sourceBranch base noQuantum m ell width modulus inverse outputs unit position Reference store
      outcome
  have preparation : native * full = full * source := by
    have actual := preparationAction_intertwines (environment := environment)
      base noQuantum m ell width modulus positive inverse outputs unit position Reference store
    simpa only [native, full, source] using actual
  have reset : resetNative * full = full * resetSource :=
    ContextReset.resetRow_intertwines base noQuantum m ell width modulus positive Reference outcome
  have half : branchSource * zero = zero * result := by
    have actual := NativeBranch.reference_intertwines _ _ _
      (ControlKraus.branch_intertwines translation phase outcome) Reference
    simpa only [branchSource, zero, result, sourceBranch, translation, phase] using actual
  have sourceProduct : resetSource * source = branchSource := by
    dsimp only [resetSource, source, branchSource, sourcePreparation]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
    simp only [ControlKraus.branch, translation, phase, Matrix.mul_assoc]
  rw [zero_embedding_matrix, stageKraus]
  change (resetNative * native) * (full * zero) = (full * zero) * result
  calc
    _ = resetNative * (native * full) * zero := by simp only [Matrix.mul_assoc]
    _ = resetNative * (full * source) * zero := by rw [preparation]
    _ = full * ((resetSource * source) * zero) := by
      rw [← Matrix.mul_assoc, reset]
      simp only [Matrix.mul_assoc]
    _ = full * (branchSource * zero) := by rw [sourceProduct]
    _ = _ := by rw [half]; simp only [Matrix.mul_assoc]

/-- Encode arbitrary classical correlations with an arbitrary mixed accumulator/reference. -/
def encodeState {Reference : Register} {History : Type} [Fintype History]
    (state : ExecutionState (Store (Context base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Carrier.units modulus.val).prod Reference)) :
    State (Context base noQuantum m ell width) Reference (model.HiddenState × History) where
  block entry := BasisEmbedding.density
    (zeroEmbedding base noQuantum m ell width modulus positive Reference) (state.block entry)
  total_le_one := by
    simpa only [BasisEmbedding.basisEmbedding_density_mass] using state.total_le_one

/-- Complete actual record-conditioned clean instrument, including old values and full history. -/
lemma stage_clean_block_entry (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.val)ˣ) (position : Fin bits)
    {Reference : Register} {History : Type} [Fintype History]
    (state : ExecutionState (Store (Context base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Carrier.units modulus.val).prod Reference))
    (entry : Store (Context base noQuantum m ell width) ×
      (model.HiddenState ×
        (History ×
          (stage base noQuantum m ell width inverse outputs modulus.val unit position).Path)))
    (row column : ((Context base noQuantum m ell width).register.prod Reference).Index) :
    (((stage base noQuantum m ell width inverse outputs modulus.val unit position).execute
      environment Reference
      (encodeState base noQuantum m ell width modulus positive state)).block entry).matrix
        row column =
      ∑ source : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
        ∑ outcome : Fin 2,
          if stageRecord base noQuantum m ell width inverse outputs modulus.val unit position source
              (ContextCoordinates.physicalBit base noQuantum m ell width outcome) = entry then
            let j := BasisEmbedding.matrix
              (zeroEmbedding base noQuantum m ell width modulus positive Reference)
            let b := sourceBranch base noQuantum m ell width modulus inverse outputs unit position
              Reference source.1 outcome
            (j * (b * (state.block source).matrix * b.conjTranspose) * j.conjTranspose) row column
          else 0 := by
  rw [stage_block_entry]
  apply Finset.sum_congr rfl
  intro source _
  let outcomes : Fin 2 ≃ Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension :=
    finCongr (congrArg PNat.val (control_qubit base noQuantum m ell width)).symm
  rw [← Equiv.sum_comp outcomes]
  apply Finset.sum_congr rfl
  intro outcome _
  change (if stageRecord base noQuantum m ell width inverse outputs modulus.val unit position source
      (ContextCoordinates.physicalBit base noQuantum m ell width outcome) = entry then _ else 0) = _
  split_ifs with recorded
  · have mixed := ControlKraus.conjugation_intertwines _ _ _
      (stageKraus_intertwines (environment := environment) base noQuantum m ell width modulus
        positive inverse outputs unit
        position Reference source.1 outcome) (state.block source).matrix
    exact congrArg (fun matrix => matrix row column) mixed
  · rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.CleanStage
