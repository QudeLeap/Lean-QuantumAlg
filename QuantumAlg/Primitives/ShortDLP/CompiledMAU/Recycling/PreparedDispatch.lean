/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Seeded
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Arithmetic
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.ControlKraus
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.MemberInstrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Clean.Stage
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Placement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.InitialSeed
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Reload
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Components.Encoded.StateEmbedding
import all QuantumAlg.Core.Execution.Store.History
import all QuantumAlg.Core.Execution.Store.Blocks
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Classical.Branch
import all QuantumAlg.Core.Execution.Interpret.Laws
import all QuantumAlg.Core.Base.State.Density
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Actual preparation and stored dispatch supply the recycled member's sigma

The real initial allocation/loading
establishes the bank's seed internally. The complete reference density of
each actual Store supplies its mathematical unit-one comparison, without a
caller seed, detached density or instrument certificate. The actual selected
member reads its parameter from that same complete Store before either stream.

Only the initial prepare and the selected member are composed here. Paid
packing, the old/new classical output correspondence, full-bank restart and
the parent retry/recovery probabilities remain independent downstream steps.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.PreparedDispatch

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical (Bits)
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma branch_store_matrix {execution : ExecutionModel}
    {environment : execution.Environment}
    {pre post : RuntimeCtx execution.kind} {shape : CShape}
    (input : CInputRef pre shape) (body : shape.Value → Circuit execution pre post)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State pre Reference (execution.HiddenState × History)) (stored : Store post) :
    (((Circuit.branch input body).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ value : shape.Value,
        (((body value).execute environment Reference
          (state.selectClassical (fun entry => entry.1.read input) value)).filterClassical
            (fun entry => entry.1 = stored)).quantumMarginal.matrix := by
  let selected (value : shape.Value) :=
    (body value).execute environment Reference
      (state.selectClassical (fun entry => entry.1.read input) value)
  let extend (value : shape.Value) :
      execution.HiddenState × (History × (body value).Path) →
        execution.HiddenState × (History × (Circuit.branch input body).Path) :=
    fun history => (history.1, (history.2.1, ⟨value, history.2.2⟩))
  have distribute (result : Store post ×
      (execution.HiddenState × (History × (Circuit.branch input body).Path))) :
      (if result.1 = stored then
        ∑ value : shape.Value,
          (((selected value).mapHistory (extend value)).block result).matrix else 0) =
      ∑ value : shape.Value, if result.1 = stored then
        (((selected value).mapHistory (extend value)).block result).matrix else 0 := by
    by_cases same : result.1 = stored <;>
      simp only [same, if_true, if_false, Finset.sum_const_zero]
  change (∑ result,
    ((((Circuit.branch input body).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).block result).matrix) = _
  simp only [ExecutionState.filterClassical_block, apply_ite DensityOperator.matrix,
    DensityOperator.zero_matrix]
  simp_rw [Circuit.execute_branch_block_matrix]
  change (∑ result, if result.1 = stored then
    ∑ value : shape.Value,
      (((selected value).mapHistory (extend value)).block result).matrix else 0) = _
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro value _
  simpa only [ExecutionState.quantumMarginal, ExecutionState.filterClassical_block,
    apply_ite DensityOperator.matrix, DensityOperator.zero_matrix] using
    congrArg DensityOperator.matrix
      (State.mapHistory_store_marginal (selected value) (extend value) stored)

private lemma selected_store_input {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {shape : CShape} (input : CInputRef ctx shape) (value : shape.Value)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx) :
    ((state.selectClassical (fun entry => entry.1.read input) value).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix =
      if original.read input = value then
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      else 0 := by
  by_cases reads : original.read input = value
  · rw [if_pos reads]
    have same :
        (state.selectClassical (fun entry => entry.1.read input) value).filterClassical
            (fun entry => entry.1 = original) =
          state.filterClassical (fun entry => entry.1 = original) := by
      apply ExecutionState.ext
      intro entry
      by_cases present : entry.1 = original
      · have selected : entry.1.read input = value := present.symm ▸ reads
        simp only [ExecutionState.filterClassical_block, ExecutionState.selectClassical_block,
          if_pos present, if_pos selected]
      · simp only [ExecutionState.filterClassical_block, if_neg present]
    rw [same]
  · rw [if_neg reads]
    have zero :
        (state.selectClassical (fun entry => entry.1.read input) value).filterClassical
            (fun entry => entry.1 = original) = ExecutionState.zero := by
      apply ExecutionState.ext
      intro entry
      by_cases present : entry.1 = original
      · have absent : entry.1.read input ≠ value := present.symm ▸ reads
        simp only [ExecutionState.filterClassical_block, ExecutionState.selectClassical_block,
          if_pos present, if_neg absent, ExecutionState.zero_block]
      · simp only [ExecutionState.filterClassical_block, if_neg present,
          ExecutionState.zero_block]
    rw [zero]
    simp only [ExecutionState.quantumMarginal, ExecutionState.zero_block,
      DensityOperator.zero_matrix, Finset.sum_const_zero]

variable {environment : model.Environment}

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val] (positive : 0 < modulus.val)

/-- The clean comparison's unit-one image is exactly this bank's real loaded seed. -/
lemma zeroEmbedding_seed :
    Placement.zeroEmbedding base noQuantum m ell width modulus positive
        (1 : (Carrier.units modulus.val).Index) =
      Reload.seed base noQuantum m ell width modulus.val := by
  change Placement.basis base noQuantum m ell width
      ((Arithmetic.layout width).basisEquiv.symm
        (prodEquiv ((0 : Fin 2), (workspaceEncoding width).encode
          (Nat.FixedWidth.unitResidueWord modulus positive 1, 0)))) =
    Reload.corresponding base noQuantum m ell width
      ((Arithmetic.layout width).basisEquiv.symm
        ((Arithmetic.encoding width).encode (0, cleanWorkspace width modulus.val 1)))
  rw [cleanWorkspace_valid width modulus.val positive (Nat.le_of_lt_succ modulus.isLt)]
  rfl

/-- Any internally established seed supplies the complete actual Store/reference block. -/
lemma seeded_store_matrix {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference History)
    (seeded : BasisSeeded.Holds (Reload.seed base noQuantum m ell width modulus.val) state)
    (original : Store (Context base noQuantum m ell width)) :
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix =
      let embedding := BasisEmbedding.matrix
        (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
      embedding * (FullWordSeeded.seedDensity width modulus state original).matrix *
        embedding.conjTranspose := by
  let seed := Reload.seed base noQuantum m ell width modulus.val
  ext ⟨left, leftRef⟩ ⟨right, rightRef⟩
  have reference :
      (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
          leftRef rightRef =
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef) := by
    change (DensityOperator.marginalLeft
      (DensityOperator.reindex (S := Reference.prod (Context base noQuantum m ell width).register)
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal
        (Equiv.prodComm
          (Context base noQuantum m ell width).register.Index Reference.Index))).matrix
          leftRef rightRef = _
    rw [DensityOperator.marginalLeft_matrix]
    simp only [DensityOperator.reindex_entry]
    exact BasisSeeded.reference_entry seed state seeded original leftRef rightRef
  let sourceEmbedding : Matrix (Context base noQuantum m ell width).register.Index
      (Carrier.units modulus.val).Index ℂ :=
    BasisEmbedding.matrix (Placement.zeroEmbedding base noQuantum m ell width modulus positive)
  let framedEmbedding : Matrix
      ((Context base noQuantum m ell width).register.prod Reference).Index
      ((Carrier.units modulus.val).prod Reference).Index ℂ :=
    BasisEmbedding.matrix
      (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
  let tensorEmbedding : Matrix
      ((Context base noQuantum m ell width).register.prod Reference).Index
      ((Carrier.units modulus.val).prod Reference).Index ℂ :=
    sourceEmbedding ⊗ₖ (1 : HilbertOperator Reference)
  let density : Matrix ((Carrier.units modulus.val).prod Reference).Index
      ((Carrier.units modulus.val).prod Reference).Index ℂ :=
    (FullWordSeeded.seedDensity width modulus state original).matrix
  have embeddingSame : framedEmbedding = tensorEmbedding :=
    BasisEmbedding.reference_matrix
      (Placement.zeroEmbedding base noQuantum m ell width modulus positive) Reference
  have branch := FullWordSeeded.tensor_seed_entry
    (Source := Carrier.units modulus.val)
    (Target := (Context base noQuantum m ell width).register) (Reference := Reference)
    sourceEmbedding (1 : (Carrier.units modulus.val).Index)
    (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal
    left right leftRef rightRef
  change (tensorEmbedding * density * tensorEmbedding.conjTranspose)
    (left, leftRef) (right, rightRef) = _ at branch
  have transported := congrArg
    (fun operator : Matrix
        ((Context base noQuantum m ell width).register.prod Reference).Index
        ((Carrier.units modulus.val).prod Reference).Index ℂ =>
      (operator * density * operator.conjTranspose) (left, leftRef) (right, rightRef))
    embeddingSame
  have actualBranch := transported.trans branch
  rw [reference] at actualBranch
  have placedSeed :
      Placement.zeroEmbedding base noQuantum m ell width modulus positive
          (1 : (Carrier.units modulus.val).Index) = seed :=
    zeroEmbedding_seed base noQuantum m ell width modulus positive
  have sourceColumn (row : (Context base noQuantum m ell width).register.Index) :
      sourceEmbedding row 1 = if row = seed then (1 : ℂ) else 0 := by
    have matching :
        Placement.zeroEmbedding base noQuantum m ell width modulus positive
            (1 : (Carrier.units modulus.val).Index) = row ↔ row = seed := by
      constructor
      · intro same
        exact same.symm.trans placedSeed
      · intro same
        exact placedSeed.trans same.symm
    change (if Placement.zeroEmbedding base noQuantum m ell width modulus positive
      (1 : (Carrier.units modulus.val).Index) = row then (1 : ℂ) else 0) = _
    exact if_congr matching rfl rfl
  have column :
      sourceEmbedding left 1 *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef) *
        star (sourceEmbedding right 1) =
      if left = seed ∧ right = seed then
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef) else 0 := by
    rw [sourceColumn left, sourceColumn right]
    by_cases first : left = seed <;> by_cases second : right = seed <;>
      simp only [first, second, and_self, and_false, false_and, if_true, if_false,
        star_one, star_zero, one_mul, zero_mul, mul_one, mul_zero]
  exact (seeded original left right leftRef rightRef).trans (actualBranch.trans column).symm

/-- Actual allocation and loading derive every complete Store's full reference density. -/
lemma prepared_store_matrix {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History))
    (original : Store (Context base noQuantum m ell width)) :
    ((((prepare base noQuantum m ell width modulus.val).execute environment Reference
      state).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix) =
      let initialized := (prepare base noQuantum m ell width modulus.val).execute environment
        Reference state
      let embedding := BasisEmbedding.matrix
        (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
      embedding * (FullWordSeeded.seedDensity width modulus initialized original).matrix *
        embedding.conjTranspose := by
  exact seeded_store_matrix base noQuantum m ell width modulus positive
    ((prepare base noQuantum m ell width modulus.val).execute environment Reference state)
    (InitialSeed.recyclingPrepare_seeded base noQuantum m ell width modulus.val state) original

private lemma selected_store_matrix {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape) (N : Nat)
    (generator target : shape.Value → (ZMod N)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (stored : Store (Context base noQuantum m ell width)) :
    (((Round.selected base noQuantum m ell width parameter N generator target).execute environment
      Reference state).filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          if MemberInstrument.memberStore base noQuantum m ell width original outcome = stored then
            let operator := MemberInstrument.memberKraus (environment := environment) base
              noQuantum m ell width N
              (generator (original.read parameter)) (target (original.read parameter))
                Reference original outcome
            operator *
              (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
                operator.conjTranspose
          else 0 := by
  rw [Round.selected, branch_store_matrix]
  simp_rw [MemberInstrument.member_store_matrix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  simp_rw [selected_store_input]
  have dispatch (value : shape.Value) :
      (if MemberInstrument.memberStore base noQuantum m ell width original outcome = stored then
        let operator := MemberInstrument.memberKraus (environment := environment) base noQuantum m
          ell width N
          (generator value) (target value) Reference original outcome
        operator *
          (if original.read parameter = value then
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          else 0) * operator.conjTranspose else 0) =
      if original.read parameter = value then
        (if MemberInstrument.memberStore base noQuantum m ell width original outcome = stored then
          let operator := MemberInstrument.memberKraus (environment := environment) base noQuantum
            m ell width N
            (generator value) (target value) Reference original outcome
          operator *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              operator.conjTranspose else 0)
      else 0 := by
    by_cases reads : original.read parameter = value <;>
      simp only [reads, if_true, if_false, Matrix.mul_zero, Matrix.zero_mul, ite_self]
  simp_rw [dispatch]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Stored parameter selection retains the full posterior of an internally established seed. -/
lemma seeded_selected_store_matrix {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape)
    (generator target : shape.Value → (ZMod modulus.val)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (Reload.seed base noQuantum m ell width modulus.val) state)
    (stored : Store (Context base noQuantum m ell width)) :
    (((Round.selected base noQuantum m ell width parameter modulus.val generator
        target).execute environment Reference state).filterClassical
          (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      let embedding := BasisEmbedding.matrix
        (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          if MemberInstrument.memberStore base noQuantum m ell width original outcome = stored then
            embedding * MemberInstrument.memberSigma base noQuantum m ell width modulus
              (generator (original.read parameter)) (target (original.read parameter)) Reference
                original outcome (FullWordSeeded.seedDensity width modulus state original).matrix *
              embedding.conjTranspose
          else 0 := by
  rw [selected_store_matrix]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  split_ifs with reached
  · rw [seeded_store_matrix base noQuantum m ell width modulus positive state seeded]
    rw [MemberInstrument.memberSigma_eq_product]
    exact ControlKraus.conjugation_intertwines _ _ _
      (MemberInstrument.memberKraus_intertwines base noQuantum m ell width modulus positive
        (generator (original.read parameter)) (target (original.read parameter))
          Reference original outcome)
      (FullWordSeeded.seedDensity width modulus state original).matrix
  · rfl


/-- The actual initialized member selects its parameters and full sigma from its real Store. -/
lemma prepared_selected_store_matrix {shape : CShape}
    (parameter : CInputRef (Context base noQuantum m ell width) shape)
    (generator target : shape.Value → (ZMod modulus.val)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History))
    (stored : Store (Context base noQuantum m ell width)) :
    ((((prepare base noQuantum m ell width modulus.val).seq
      (Round.selected base noQuantum m ell width parameter modulus.val generator
        target)).execute environment Reference state).filterClassical
          (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      let initialized := (prepare base noQuantum m ell width modulus.val).execute environment
        Reference state
      let embedding := BasisEmbedding.matrix
        (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          if MemberInstrument.memberStore base noQuantum m ell width original outcome = stored then
            embedding * MemberInstrument.memberSigma base noQuantum m ell width modulus
              (generator (original.read parameter)) (target (original.read parameter)) Reference
                original outcome
                  (FullWordSeeded.seedDensity width modulus initialized original).matrix *
              embedding.conjTranspose
          else 0 := by
  refine (congrArg DensityOperator.matrix (Circuit.seq_store_marginal (environment := environment)
    (prepare base noQuantum m ell width modulus.val)
    (Round.selected base noQuantum m ell width parameter modulus.val generator target)
    state stored)).trans ?_
  exact seeded_selected_store_matrix base noQuantum m ell width modulus positive parameter
    generator target ((prepare base noQuantum m ell width modulus.val).execute environment
      Reference state)
    (InitialSeed.recyclingPrepare_seeded base noQuantum m ell width modulus.val state) stored

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.PreparedDispatch
