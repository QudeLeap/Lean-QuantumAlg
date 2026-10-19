/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.PackedSample
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Scope.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program.Store
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
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

/-!
# Actual uniform sources on the preallocated RSA frame

One real random instruction writes the source bits, and the original scoped
sampler computes the complete parameter from those bits. Arbitrary weights on
the complete returned store retain the exact uniform source coefficient and
both external reference coordinates. This applies before the sole bank
allocation and to every later draw on the existing bank.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

open Execution ClassicalRoutines
open EkeraHastadStyle.Canonical

variable {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (N : Nat) {ctx : RuntimeCtx .quantum}
  (sample : CWriteRef ctx (.bits (residueSamplingBits N)))
  (parameter : CWriteRef ctx (ParameterShape N))

/-- Complete caller store after the actual source draw and actual parameter computation. -/
def sourceStore (before : Store ctx) (value : Fin (2 ^ residueSamplingBits N)) : Store ctx :=
  (ShorStyle.Canonical.Sampler.Program.step
    (model := ShortDLP.CompiledMAU.Recycling.model) N (FirstAccepted.cellRead sample) parameter
    (before.write sample (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))).1

/-- The actual scoped computation writes the parameter of that identical native random draw. -/
lemma rsaRecyclingParent_sourceStore_value (input : Input N) (before : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) :
    sourceStore N sample parameter before value =
      (before.write sample
        (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))).write parameter
          (parameterValue input value) := by
  exact ShorStyle.Canonical.Sampler.Program.samplerProgram_store
    (model := ShortDLP.CompiledMAU.Recycling.model) input.samplerInput
    (FirstAccepted.cellRead sample) parameter
    (before.write sample (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))) value
    (show (before.write sample
      (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value))).read
        (FirstAccepted.cellRead sample) = _ from Store.read_write_same before sample _)

/-- The complete stored parameter is the one computed from the source actually drawn. -/
lemma rsaRecyclingParent_sourceStore_parameter (input : Input N) (before : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) :
    (sourceStore N sample parameter before value).read (FirstAccepted.cellRead parameter) =
      parameterValue input value :=
  (congrArg (fun store : Store ctx => store.read (FirstAccepted.cellRead parameter))
    (rsaRecyclingParent_sourceStore_value N sample parameter input before value)).trans
      (Store.read_write_same _ parameter _)

/-- A distinct parameter destination preserves the source bits of the same actual draw. -/
lemma rsaRecyclingParent_sourceStore_sample (input : Input N) (before : Store ctx)
    (value : Fin (2 ^ residueSamplingBits N)) (separate : parameter.key ≠ sample.key) :
    (sourceStore N sample parameter before value).read (FirstAccepted.cellRead sample) =
      .bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value) :=
  (congrArg (fun store : Store ctx => store.read (FirstAccepted.cellRead sample))
    (rsaRecyclingParent_sourceStore_value N sample parameter input before value)).trans
      ((Store.read_write_other _ parameter sample.toCStorageRef _ separate).trans
        (Store.read_write_same before sample _))

/-- The actual native draw preserves basis support in every complete final storage block. -/
lemma rsaRecyclingParent_sourceDraw_seeded (seed : ctx.register.Index)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds seed
      ((ShorStyle.Canonical.Sampler.PackedSample.draw
        (model := ShortDLP.CompiledMAU.Recycling.model) N sample).execute environment
          Reference state) := by
  apply BasisSeeded.of_block_marginal_support seed
  intro finalStore basis outside
  rw [DensityOperator.marginalLeft_matrix]
  have absent (entry : Store ctx ×
      (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
      (reference : Reference.Index) :
      (state.block entry).matrix (basis, reference) (basis, reference) = 0 :=
    BasisSeeded.block_diagonal_zero seed state seeded entry basis outside reference
  simp only [ShorStyle.Canonical.Sampler.PackedSample.packedSample_draw_block_matrix,
    Matrix.sum_apply, Matrix.ite_apply, Matrix.smul_apply, Matrix.zero_apply,
    absent, smul_zero, ite_self, Finset.sum_const_zero]

/-- The real source draw and parameter computation preserve the internally established seed. -/
lemma rsaRecyclingParent_source_seeded (seed : ctx.register.Index)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
    (seeded : BasisSeeded.Holds seed state) :
    BasisSeeded.Holds seed ((source N sample parameter).execute environment Reference state) := by
  let draw : Circuit ShortDLP.CompiledMAU.Recycling.model ctx ctx :=
    ShorStyle.Canonical.Sampler.PackedSample.draw
      (model := ShortDLP.CompiledMAU.Recycling.model) N sample
  let compute : Circuit ShortDLP.CompiledMAU.Recycling.model ctx ctx :=
    ShorStyle.Canonical.Sampler.Program.circuit
      (model := ShortDLP.CompiledMAU.Recycling.model) N (FirstAccepted.cellRead sample) parameter
  apply BasisSeeded.seq (environment := environment) (model := ShortDLP.CompiledMAU.Recycling.model)
    draw compute seed state
  have actual := ShorStyle.Canonical.Sampler.Program.samplerProgram_execute (environment :=
    environment)
    (model := ShortDLP.CompiledMAU.Recycling.model) N (FirstAccepted.cellRead sample) parameter
    Reference (draw.execute environment Reference state)
  rw [show compute.execute environment Reference (draw.execute environment Reference state) =
    _ from actual]
  exact BasisSeeded.mapStore seed _ (rsaRecyclingParent_sourceDraw_seeded N sample seed
    state seeded)
    (fun store => (ShorStyle.Canonical.Sampler.Program.step
      (model := ShortDLP.CompiledMAU.Recycling.model) N
      (FirstAccepted.cellRead sample) parameter store).1)
    (fun entry => (entry.2.1, (entry.2.2,
      (ShorStyle.Canonical.Sampler.Program.step
        (model := ShortDLP.CompiledMAU.Recycling.model) N
        (FirstAccepted.cellRead sample) parameter entry.1).2)))

/-- The same actual source law covers the first frame draw and every subsequent bank draw. -/
lemma rsaRecyclingParent_source_referenceFiberSum
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History))
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
        (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History)) →
        ctx.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe left right)
  funext entry basis
  apply Finset.sum_congr rfl
  intro value _
  dsimp only
  exact congrArg
    (fun scalar : ℂ => scalar * weight
      ((ShorStyle.Canonical.Sampler.Program.step
        (model := ShortDLP.CompiledMAU.Recycling.model) N
        (FirstAccepted.cellRead sample) parameter
        (entry.1.write sample
          (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)))).1))
    (Complex.ofReal_inv ((2 ^ residueSamplingBits N : Nat) : ℝ))

end

end QuantumAlg.Factoring.RSA.Recycling.Program
