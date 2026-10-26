/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Measured.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.PackedSample
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Scope.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Store
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Context
import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Random.Observation
import all QuantumAlg.Core.Execution.Measurement.Fibers
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Basis.Seeded.Record
import all QuantumAlg.Core.Execution.Basis.Seeded.Admission
import all QuantumAlg.Core.Execution.Basis.Seeded.Processing
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Base.State.Density
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport.Store

/-!
# Actual uniform sources on the preallocated RSA frame

One real random instruction writes the source bits, and the original scoped
sampler computes the complete parameter from those bits. Arbitrary weights on
the complete returned store retain the exact uniform source coefficient and
both external reference coordinates [EH17, source.tex:878-966]. This applies before the sole bank
allocation and to every later draw on the existing bank.
-/

namespace QuantumAlg.Factoring.RSA.Measured.Program

noncomputable section

variable [configuration : Configuration]

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical

variable {environment : MeasuredRSAModel.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (N : Nat) {ctx : RuntimeCtx .quantum}
  (sample : CWriteRef ctx (.bits (residueSamplingBits N)))
  (parameter : CWriteRef ctx (ParameterShape N))

/-- Complete caller store after the actual source draw and actual parameter computation. -/
def sourceStore (before : Store ctx) (value : Fin (2 ^ residueSamplingBits N)) : Store ctx :=
  (ShorStyle.Canonical.Sampler.Program.step
    (model := MeasuredRSAModel) N (FirstAccepted.cellRead sample) parameter
    (before.write sample (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))).1

omit configuration in
/-- The actual scoped computation writes the parameter of that identical native random draw. -/
lemma rsaMeasuredParent_sourceStore_value (input : Input N) (before : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) :
    sourceStore N sample parameter before value =
      (before.write sample
        (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))).write parameter
          (parameterValue input value) := by
  exact ShorStyle.Canonical.Sampler.Program.samplerProgram_store
    (model := MeasuredRSAModel) input.samplerInput
    (FirstAccepted.cellRead sample) parameter
    (before.write sample (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))) value
    (show (before.write sample
      (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))).read
        (FirstAccepted.cellRead sample) = _ from Store.read_write_same before sample _)

omit configuration in
/-- The complete stored parameter is the one computed from the source actually drawn. -/
lemma rsaMeasuredParent_sourceStore_parameter (input : Input N) (before : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) :
    (sourceStore N sample parameter before value).read (FirstAccepted.cellRead parameter) =
      parameterValue input value :=
  (congrArg (fun store : Store ctx => store.read (FirstAccepted.cellRead parameter))
    (rsaMeasuredParent_sourceStore_value N sample parameter input before value)).trans
      (Store.read_write_same _ parameter _)

omit configuration in
/-- A distinct parameter destination preserves the source bits of the same actual draw. -/
lemma rsaMeasuredParent_sourceStore_sample (input : Input N) (before : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) (separate : parameter.key ≠ sample.key) :
    (sourceStore N sample parameter before value).read (FirstAccepted.cellRead sample) =
      .bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value) :=
  (congrArg (fun store : Store ctx => store.read (FirstAccepted.cellRead sample))
    (rsaMeasuredParent_sourceStore_value N sample parameter input before value)).trans
      ((Store.read_write_other _ parameter sample.toCStorageRef _ separate).trans
        (Store.read_write_same before sample _))

omit configuration in
/-- The actual native draw preserves basis support in every complete final storage block. -/
lemma rsaMeasuredParent_sourceDraw_seeded (seed : ctx.register.Index)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds seed
      ((ShorStyle.Canonical.Sampler.PackedSample.draw
        (model := MeasuredRSAModel) N sample).execute environment
          Reference state) := by
  apply BasisSeeded.of_block_marginal_support seed
  intro finalStore basis outside
  rw [DensityOperator.marginalLeft_matrix]
  have absent (entry : Store ctx ×
      (MeasuredRSAModel.HiddenState × History))
      (reference : Reference.Index) :
      (state.block entry).matrix (basis, reference) (basis, reference) = 0 :=
    BasisSeeded.block_diagonal_zero seed state seeded entry basis outside reference
  simp only [ShorStyle.Canonical.Sampler.PackedSample.packedSample_draw_block_matrix,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.smul_apply, Matrix.zero_apply,
    absent, smul_zero, ite_self, Finset.sum_const_zero]

omit configuration in
/-- The real source draw and parameter computation preserve the internally established seed. -/
lemma rsaMeasuredParent_source_seeded (seed : ctx.register.Index)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (MeasuredRSAModel.HiddenState × History))
    (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds seed ((source N sample parameter).execute environment Reference state) := by
  let draw : Circuit MeasuredRSAModel ctx ctx :=
    ShorStyle.Canonical.Sampler.PackedSample.draw
      (model := MeasuredRSAModel) N sample
  let compute : Circuit MeasuredRSAModel ctx ctx :=
    ShorStyle.Canonical.Sampler.Program.circuit
      (model := MeasuredRSAModel) N (FirstAccepted.cellRead sample) parameter
  apply BasisSeeded.seq (environment := environment) (model := MeasuredRSAModel)
    draw compute seed state
  have actual := ShorStyle.Canonical.Sampler.Program.samplerProgram_execute (environment :=
    environment)
    (model := MeasuredRSAModel) N (FirstAccepted.cellRead sample) parameter
    Reference (draw.execute environment Reference state)
  rw [show compute.execute environment Reference (draw.execute environment Reference state) =
    _ from actual]
  exact BasisSeeded.mapStore seed _ (rsaMeasuredParent_sourceDraw_seeded N sample seed
    state seeded)
    (fun store => (ShorStyle.Canonical.Sampler.Program.step
      (model := MeasuredRSAModel) N
      (FirstAccepted.cellRead sample) parameter store).1)
    (fun entry => (entry.2.1, (entry.2.2,
      (ShorStyle.Canonical.Sampler.Program.step
        (model := MeasuredRSAModel) N
        (FirstAccepted.cellRead sample) parameter entry.1).2)))

omit configuration in
/-- The same actual source law covers the first frame draw and every subsequent bank draw. -/
lemma rsaMeasuredParent_source_referenceFiberSum
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (MeasuredRSAModel.HiddenState × History))
    (weight : Store ctx → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((source N sample parameter).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            weight (sourceStore N sample parameter entry.1 value)) left right := by
  unfold sourceStore
  unfold source
  rw [Circuit.referenceFiberSum_execute_seq,
    ShorStyle.Canonical.Sampler.Program.samplerProgram_execute,
    ExecutionState.referenceFiberSum_mapClassical,
    ShorStyle.Canonical.Sampler.PackedSample.packedSample_draw_execute,
    ExecutionState.referenceFiberSum_mapClassical]
  refine (referenceFiberSum_uniformChoice state
    (⟨2 ^ residueSamplingBits N, Nat.two_pow_pos _⟩ : ℕ+) _ left right).trans ?_
  apply congrArg
    (fun observe : (Store ctx ×
        (MeasuredRSAModel.HiddenState × History)) →
        ctx.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  apply Finset.sum_congr rfl
  intro value _
  dsimp only
  exact congrArg
    (fun scalar : ℂ => scalar * weight
      ((ShorStyle.Canonical.Sampler.Program.step
        (model := MeasuredRSAModel) N
        (FirstAccepted.cellRead sample) parameter
        (entry.1.write sample
          (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))).1))
    (Complex.ofReal_inv ((2 ^ residueSamplingBits N : Nat) : ℝ))

omit configuration in
/-- The actual source's two paid writes commute with complete caller-Store transport. -/
lemma rsaMeasuredParent_sourceStore_transport {outer inner : RuntimeCtx .quantum}
    (transport : ClassicalWorkspace.Transport outer inner)
    (sample : CWriteRef outer (.bits (residueSamplingBits N)))
    (parameter : CWriteRef outer (ParameterShape N)) (input : Input N)
    (before : Store inner) (value : Fin (2 ^ residueSamplingBits N)) :
    transport.restrict
      (sourceStore N (transport.liftWrite sample) (transport.liftWrite parameter) before value) =
      sourceStore N sample parameter (transport.restrict before) value := by
  rw [rsaMeasuredParent_sourceStore_value N (transport.liftWrite sample)
    (transport.liftWrite parameter) input,
    rsaMeasuredParent_sourceStore_value N sample parameter input,
    transport.workspaceTransport_restrict_write, transport.workspaceTransport_restrict_write]

omit configuration in
/-- Real fresh-source execution retains the caller's full Store and both Reference indices. -/
lemma rsaMeasuredParent_source_parent_referenceFiberSum {outer inner : RuntimeCtx .quantum}
    (transport : ClassicalWorkspace.Transport outer inner)
    (sample : CWriteRef outer (.bits (residueSamplingBits N)))
    (parameter : CWriteRef outer (ParameterShape N)) (input : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State inner Reference (MeasuredRSAModel.HiddenState × History))
    (weight : Store outer → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((source N (transport.liftWrite sample) (transport.liftWrite parameter)).execute
        environment Reference state)
      (fun entry _ => weight (transport.restrict entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ value : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            weight (sourceStore N sample parameter (transport.restrict entry.1) value))
        left right := by
  refine (rsaMeasuredParent_source_referenceFiberSum N (transport.liftWrite sample)
    (transport.liftWrite parameter) state (fun stored => weight (transport.restrict stored))
    left right).trans ?_
  apply congrArg (fun observe => ExecutionState.referenceFiberSum state observe left right)
  funext entry _basis
  apply Finset.sum_congr rfl
  intro value _
  exact congrArg
    (fun stored => (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * weight stored)
    (rsaMeasuredParent_sourceStore_transport N transport sample parameter input entry.1 value)

end

end QuantumAlg.Factoring.RSA.Measured.Program
