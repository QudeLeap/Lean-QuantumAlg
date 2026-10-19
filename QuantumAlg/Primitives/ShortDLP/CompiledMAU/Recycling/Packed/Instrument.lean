/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.PreparedDispatch
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Measurement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Seeded
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Packing
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.InitialSeed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Reload
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.MemberInstrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Clean.Stage
import all QuantumAlg.Components.Encoded.StateEmbedding
import all QuantumAlg.Components.Classical.Model.BitWord.Execution
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Store.History
import all QuantumAlg.Core.Execution.Store.Blocks
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Execution.Measured.FeedForward

/-!
# Full stored instrument after actual paid packing

The real selected classical instruction
pushes each complete incoming Store to its actual applyOp result. All input
fibers reaching the same destination are summed, including write collisions.
The reusable theorem composes the actual selected two-stream member and paid
instruction from an internally established seed. Its preparation corollary
derives that seed by the real program, without a caller seed certificate.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.PackedInstrument

noncomputable section

variable {environment : model.Environment}

open Execution
open QuantumFourierTransform.Semiclassical (Bits)
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The actual paid instruction sums every complete Store fiber with this real destination. -/
lemma packing_store_matrix
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (stored : Store (Context base noQuantum m ell width)) :
    (((Packing.code base noQuantum m ell width result).execute environment Reference
      state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store (Context base noQuantum m ell width),
        if original.applyOp (Packing.operation base noQuantum m ell width result) = stored then
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        else 0 := by
  apply Matrix.ext
  intro left right
  rw [ExecutionState.filterClassical_matrix_weighted, Packing.recyclingPacking_execute]
  let update : Store (Context base noQuantum m ell width) × (model.HiddenState × History) →
      Store (Context base noQuantum m ell width) ×
        (model.HiddenState × (History × (Packing.code base noQuantum m ell width result).Path)) :=
    fun entry =>
      let next := BitWord.instructionStep (execution := model)
        (Packing.operation base noQuantum m ell width result) entry.1
      (next.1, (entry.2.1, (entry.2.2, next.2)))
  refine (ExecutionState.weightedMatrixEntry_mapClassical state update
    (fun entry => if entry.1 = stored then (1 : ℂ) else 0) left right).trans ?_
  change ExecutionState.weightedMatrixEntry state
    (fun entry => if entry.1.applyOp (Packing.operation base noQuantum m ell width result) = stored
      then 1 else 0) left right = _
  refine (FullWordMeasurement.weighted_store state
    (fun original =>
      if original.applyOp (Packing.operation base noQuantum m ell width result) = stored
        then (1 : ℂ) else 0) left right).trans ?_
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply, ite_mul, one_mul, zero_mul]

/-- Eliminate only the intermediate Store; the real packing write remains in the condition. -/
private lemma packing_member_sum
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    {Reference : Register}
    (weight : Store (Context base noQuantum m ell width) → Bits (ell + m) × Bits ell →
      HilbertOperator ((Context base noQuantum m ell width).register.prod Reference))
    (stored : Store (Context base noQuantum m ell width)) :
    (∑ middle : Store (Context base noQuantum m ell width),
      if middle.applyOp (Packing.operation base noQuantum m ell width result) = stored then
        ∑ original : Store (Context base noQuantum m ell width),
          ∑ outcome : Bits (ell + m) × Bits ell,
            if MemberInstrument.memberStore base noQuantum m ell width original outcome = middle
              then weight original outcome else 0
      else 0) =
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          if (MemberInstrument.memberStore base noQuantum m ell width original outcome).applyOp
              (Packing.operation base noQuantum m ell width result) = stored then
            weight original outcome
          else 0 := by
  have distribute (middle : Store (Context base noQuantum m ell width)) :
      (if middle.applyOp (Packing.operation base noQuantum m ell width result) = stored then
        ∑ original : Store (Context base noQuantum m ell width),
          ∑ outcome : Bits (ell + m) × Bits ell,
            if MemberInstrument.memberStore base noQuantum m ell width original outcome = middle
              then weight original outcome else 0
      else 0) =
        ∑ original : Store (Context base noQuantum m ell width),
          ∑ outcome : Bits (ell + m) × Bits ell,
            if MemberInstrument.memberStore base noQuantum m ell width original outcome = middle
              then
                if middle.applyOp (Packing.operation base noQuantum m ell width result) = stored
                  then weight original outcome else 0
              else 0 := by
    by_cases reached : middle.applyOp (Packing.operation base noQuantum m ell width result) = stored
    · simp only [reached, if_true]
    · simp only [reached, if_false, ite_self, Finset.sum_const_zero]
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Actual sampled dispatch and paid packing preserve every internally seeded posterior. -/
lemma seeded_sampled_store_matrix
    (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val] (positive : 0 < modulus.val)
    {shape : CShape} (parameter : CInputRef (Context base noQuantum m ell width) shape)
    (generator target : shape.Value → (ZMod modulus.val)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (Reload.seed base noQuantum m ell width modulus.val) state)
    (stored : Store (Context base noQuantum m ell width)) :
    (((Round.sampled base noQuantum m ell width parameter modulus.val
        generator target result).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      let embedding := BasisEmbedding.matrix
        (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          if (MemberInstrument.memberStore base noQuantum m ell width original outcome).applyOp
              (Packing.operation base noQuantum m ell width result) = stored then
            embedding * MemberInstrument.memberSigma base noQuantum m ell width modulus
              (generator (original.read parameter)) (target (original.read parameter)) Reference
                original outcome (FullWordSeeded.seedDensity width modulus state original).matrix *
              embedding.conjTranspose
          else 0 := by
  let embedding := BasisEmbedding.matrix
    (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
  let weight (original : Store (Context base noQuantum m ell width))
      (outcome : Bits (ell + m) × Bits ell) :=
    embedding * MemberInstrument.memberSigma base noQuantum m ell width modulus
      (generator (original.read parameter)) (target (original.read parameter)) Reference
        original outcome (FullWordSeeded.seedDensity width modulus state original).matrix *
      embedding.conjTranspose
  have selected (middle : Store (Context base noQuantum m ell width)) :
      (((Round.selected base noQuantum m ell width parameter modulus.val
          generator target).execute environment Reference state).filterClassical
        (fun entry => entry.1 = middle)).quantumMarginal.matrix =
        ∑ original : Store (Context base noQuantum m ell width),
          ∑ outcome : Bits (ell + m) × Bits ell,
            if MemberInstrument.memberStore base noQuantum m ell width original outcome = middle
              then weight original outcome else 0 :=
    PreparedDispatch.seeded_selected_store_matrix base noQuantum m ell width modulus positive
      parameter generator target state seeded middle
  rw [Round.sampled]
  refine (congrArg DensityOperator.matrix (Circuit.seq_store_marginal (environment := environment)
    (Round.selected base noQuantum m ell width parameter modulus.val generator target)
    (Packing.code base noQuantum m ell width result) state stored)).trans ?_
  rw [packing_store_matrix]
  simp_rw [selected]
  exact packing_member_sum base noQuantum m ell width result weight stored

/-- Real prepare and sampled execute the internally supplied sigma and actual charged write. -/
lemma prepared_sampled_store_matrix
    (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val] (positive : 0 < modulus.val)
    {shape : CShape} (parameter : CInputRef (Context base noQuantum m ell width) shape)
    (generator target : shape.Value → (ZMod modulus.val)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History))
    (stored : Store (Context base noQuantum m ell width)) :
    ((((prepare base noQuantum m ell width modulus.val).seq
      (Round.sampled base noQuantum m ell width parameter modulus.val generator target
        result)).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      let initialized := (prepare base noQuantum m ell width modulus.val).execute environment
        Reference state
      let embedding := BasisEmbedding.matrix
        (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          if (MemberInstrument.memberStore base noQuantum m ell width original outcome).applyOp
              (Packing.operation base noQuantum m ell width result) = stored then
            embedding * MemberInstrument.memberSigma base noQuantum m ell width modulus
              (generator (original.read parameter)) (target (original.read parameter)) Reference
                original outcome
                  (FullWordSeeded.seedDensity width modulus initialized original).matrix *
              embedding.conjTranspose
          else 0 := by
  refine (congrArg DensityOperator.matrix (Circuit.seq_store_marginal (environment := environment)
    (prepare base noQuantum m ell width modulus.val)
    (Round.sampled base noQuantum m ell width parameter modulus.val generator target result)
    state stored)).trans ?_
  exact seeded_sampled_store_matrix base noQuantum m ell width modulus positive parameter
    generator target result ((prepare base noQuantum m ell width modulus.val).execute environment
      Reference
      state) (InitialSeed.recyclingPrepare_seeded base noQuantum m ell width modulus.val state)
      stored

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.PackedInstrument
