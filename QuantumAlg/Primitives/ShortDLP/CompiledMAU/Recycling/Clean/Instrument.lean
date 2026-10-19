/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Native.Instrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Clean.Stage

/-!
# Complete actual suffix instrument on the persistent clean arithmetic carrier

The actual dynamic native branch products
intertwine with derived half-sum products on the unit accumulator. Every step
uses the same physical zero-control/zero-auxiliary embedding and the same
arbitrary Reference. The sigma recurrence is unnormalized and selected from
actual stored preceding outcomes. It does not reinitialize the accumulator or
assume commuting arithmetic on dirty input. The encoded state is an internal
mathematical comparison, never a caller certificate or a free instruction.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.CleanInstrument

noncomputable section

open Execution

variable {environment : model.Environment}
open QuantumFourierTransform.Semiclassical (Bits)
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val] (positive : 0 < modulus.val)

/-- The product uses the real preceding Store for every source half-sum branch. -/
def sourceSuffix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.val)ˣ) (Reference : Register) :
    (remaining position : Nat) → position + remaining ≤ bits →
      Store (Context base noQuantum m ell width) → Bits remaining →
        HilbertOperator ((Carrier.units modulus.val).prod Reference)
  | 0, _, _, _, _ => 1
  | remaining + 1, position, bounded, original, (outcome, tail) =>
      sourceSuffix inverse outputs unit Reference remaining
        (position + 1) (by omega)
        (original.write (outputs ⟨position, by omega⟩) (.finite outcome)) tail *
          CleanStage.sourceBranch base noQuantum m ell width modulus inverse outputs unit
            ⟨position, by omega⟩ Reference original outcome

/-- Pass the entire posterior accumulator/reference operator to the next actual bit. -/
def sigmaSuffix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.val)ˣ) (Reference : Register) :
    (remaining position : Nat) → position + remaining ≤ bits →
      Store (Context base noQuantum m ell width) → Bits remaining →
        HilbertOperator ((Carrier.units modulus.val).prod Reference) →
          HilbertOperator ((Carrier.units modulus.val).prod Reference)
  | 0, _, _, _, _, density => density
  | remaining + 1, position, bounded, original, (outcome, tail), density =>
      let branch := CleanStage.sourceBranch base noQuantum m ell width modulus inverse outputs
        unit ⟨position, by omega⟩ Reference original outcome
      sigmaSuffix inverse outputs unit Reference remaining
        (position + 1) (by omega)
        (original.write (outputs ⟨position, by omega⟩) (.finite outcome)) tail
          (branch * density * branch.conjTranspose)

/-- The common-reference posterior is exactly the chronological half-sum product. -/
lemma sigmaSuffix_eq_product (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.val)ˣ) (Reference : Register) (remaining position : Nat)
    (bounded : position + remaining ≤ bits) (original : Store (Context base noQuantum m ell width))
    (outcome : Bits remaining)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    sigmaSuffix base noQuantum m ell width modulus inverse outputs unit Reference remaining
        position bounded original outcome density =
      sourceSuffix base noQuantum m ell width modulus inverse outputs unit Reference remaining
          position bounded original outcome * density *
        (sourceSuffix base noQuantum m ell width modulus inverse outputs unit Reference remaining
          position bounded original outcome).conjTranspose := by
  induction remaining generalizing position original density with
  | zero => simp only [sigmaSuffix, sourceSuffix, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one]
  | succ remaining induction =>
      rcases outcome with ⟨head, tail⟩
      rw [sigmaSuffix, induction]
      simp only [sourceSuffix, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Every actual physical branch product preserves the same clean carrier with its Reference. -/
lemma suffixKraus_intertwines (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.val)ˣ) (Reference : Register) (remaining position : Nat)
    (bounded : position + remaining ≤ bits) (original : Store (Context base noQuantum m ell width))
    (outcome : Bits remaining) :
    NativeInstrument.suffixKraus (environment := environment) base noQuantum m ell width inverse
      outputs modulus.val unit
        Reference remaining position bounded original outcome *
      BasisEmbedding.matrix
        (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference) =
    BasisEmbedding.matrix
        (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference) *
      sourceSuffix base noQuantum m ell width modulus inverse outputs unit Reference remaining
        position bounded original outcome := by
  induction remaining generalizing position original with
  | zero => simp only [NativeInstrument.suffixKraus, sourceSuffix,
      Matrix.one_mul, Matrix.mul_one]
  | succ remaining induction =>
      rcases outcome with ⟨head, tail⟩
      rw [NativeInstrument.suffixKraus, sourceSuffix, Matrix.mul_assoc,
        CleanStage.stageKraus_intertwines base noQuantum m ell width modulus positive]
      rw [← Matrix.mul_assoc, induction]
      simp only [Matrix.mul_assoc]

private lemma encodeState_store_matrix {Reference : Register} {History : Type} [Fintype History]
    (state : ExecutionState (Store (Context base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Carrier.units modulus.val).prod Reference))
    (original : Store (Context base noQuantum m ell width)) :
    ((CleanStage.encodeState base noQuantum m ell width modulus positive state).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix =
      let embedding := BasisEmbedding.matrix
        (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
      embedding * ((state.mapClassical (fun entry => entry.1)).block original).matrix *
        embedding.conjTranspose := by
  rw [← BasisSeeded.store_matrix]
  simp only [ExecutionState.mapClassical_block_matrix, CleanStage.encodeState,
    BasisEmbedding.density]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro source _
  by_cases selected : source.1 = original
  · simp only [selected, if_true]
  · simp only [selected, if_false, Matrix.mul_zero, Matrix.zero_mul]

/-- The full real suffix evolves each actual stored branch by the common-reference sigma law. -/
lemma exponentSuffix_clean_store_matrix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (unit : (ZMod modulus.val)ˣ) (remaining position : Nat) (bounded : position + remaining ≤ bits)
    {Reference : Register} {History : Type} [Fintype History]
    (state : ExecutionState (Store (Context base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Carrier.units modulus.val).prod Reference))
    (stored : Store (Context base noQuantum m ell width)) :
    ((exponentSuffix base noQuantum m ell width inverse outputs modulus.val unit remaining position
      bounded).execute environment Reference
        (CleanStage.encodeState base noQuantum m ell width modulus positive state)
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store (Context base noQuantum m ell width), ∑ outcome : Bits remaining,
        if NativeInstrument.suffixStore base noQuantum m ell width inverse outputs remaining
            position bounded original outcome = stored then
          let embedding := BasisEmbedding.matrix
            (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
          embedding *
            sigmaSuffix base noQuantum m ell width modulus inverse outputs unit Reference remaining
              position bounded original outcome
              ((state.mapClassical (fun entry => entry.1)).block original).matrix *
            embedding.conjTranspose
        else 0 := by
  rw [NativeInstrument.exponentSuffix_store_matrix]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  split_ifs with reached
  · rw [encodeState_store_matrix base noQuantum m ell width modulus positive]
    rw [sigmaSuffix_eq_product]
    exact ControlKraus.conjugation_intertwines _ _ _
      (suffixKraus_intertwines base noQuantum m ell width modulus positive inverse outputs unit
        Reference remaining position bounded original outcome)
      ((state.mapClassical (fun entry => entry.1)).block original).matrix
  · rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.CleanInstrument
