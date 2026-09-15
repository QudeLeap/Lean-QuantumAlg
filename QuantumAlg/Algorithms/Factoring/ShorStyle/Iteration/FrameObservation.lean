/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Iteration
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Seed
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Frame
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Storage.Observation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.PackedSample

/-!
# Earlier results and one new actual Shor iteration

The old structural input, the new sampled source, its full computed parameter
and the measured phase are observed jointly with every reference coordinate.
The source weights arise from the actual fresh uniform instruction and the
actual selected circuit's Born law. This retains all correlations with the
earlier results and supplies the conditional law needed for repeated rounds.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeIteration

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Keep an earlier structural operand through the actual sampler and readout allocations. -/
def liftInput {ctx : RuntimeCtx .quantum} (N : Nat) {shape : CShape}
    (input : CInputRef ctx shape) : CInputRef (context ctx N) shape :=
  NativeStorage.liftInput (sampledContext ctx N) N
    (Sampler.Retained.liftInput (N := N) input)

private theorem storage_lift_product {ctx : RuntimeCtx .quantum} (N : Nat)
    {left right : CShape} (first : CInputRef ctx left) (second : CInputRef ctx right) :
    NativeStorage.liftInput ctx N (.product first second) =
      .product (NativeStorage.liftInput ctx N first) (NativeStorage.liftInput ctx N second) :=
  MeasurementCells.liftInput_product 2
    (first.underRetained ctx.canonicalFreshKey (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh)
    (second.underRetained ctx.canonicalFreshKey (.bits (phaseBits N)) ctx.canonicalFreshKey_fresh)
    (phaseBits N)

/-- A real iteration keeps the whole earlier-input and new-source law on every Ref entry. -/
theorem code_referenceFiberSum_input {ctx : RuntimeCtx .quantum} {N : Nat} (source : Input N)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    {shape : CShape} (input : CInputRef ctx shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) state)
    (weight : shape.Value → (CShape.bits (residueSamplingBits N)).Value →
      (ParameterShape (modulusBits N)).Value → (CShape.bits (phaseBits N)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code ctx N sameWires).execute Reference state)
        (fun entry _ => weight (entry.1.read (liftInput N input))
          (entry.1.read (sampleInput ctx N)) (entry.1.read (parameterInput ctx N))
          (entry.1.read (phaseInput ctx N))) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ sample : Fin (2 ^ residueSamplingBits N),
          (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
            ∑ outcome : OrderFinding.Outcome (phaseBits N),
              weight (entry.1.read input) (.bits (Sampler.PackedSample.storedBits sample))
                (parameterValue source sample) (.bits outcome) *
                  ((sourceSampleOutcomePMF source sample outcome).toReal : ℂ))
        leftRef rightRef := by
  let sampler := Sampler.Retained.circuit ctx N
  let sampled := sampler.execute Reference state
  let sampledWires := (sampled_quantumWires ctx N).trans sameWires
  let earlier := Sampler.Retained.liftInput (N := N) input
  let sample : CInputRef (sampledContext ctx N) (.bits (residueSamplingBits N)) :=
    .storage (Sampler.Retained.sampleRef ctx N).toCStorageRef
  let parameter : CInputRef (sampledContext ctx N) (ParameterShape (modulusBits N)) :=
    .storage (Sampler.Retained.parameterRef ctx N).toCStorageRef
  let sourceInput := CInputRef.product earlier (.product sample parameter)
  let quantumRound := NativeStorage.round (sampledContext ctx N) N sampledWires parameter
  let jointWeight :
      (CShape.product shape
        (.product (.bits (residueSamplingBits N)) (ParameterShape (modulusBits N)))).Value →
          (CShape.bits (phaseBits N)).Value → ℂ :=
    fun value phase => match value with
      | .product old (.product drawn selected) => weight old drawn selected phase
  let finalWeight := fun store : Store (context ctx N) => weight
    (store.read (liftInput N input)) (store.read (sampleInput ctx N))
    (store.read (parameterInput ctx N)) (store.read (phaseInput ctx N))
  have joined : NativeStorage.liftInput (sampledContext ctx N) N sourceInput =
      .product (liftInput N input) (.product (sampleInput ctx N) (parameterInput ctx N)) :=
    (storage_lift_product N earlier (.product sample parameter)).trans
      (congrArg (CInputRef.product (liftInput N input)) (storage_lift_product N sample parameter))
  have finalWeights : finalWeight = fun store : Store (context ctx N) =>
      jointWeight (store.read (NativeStorage.liftInput (sampledContext ctx N) N sourceInput))
        (store.read
          (.storage (NativeStorage.resultRef (sampledContext ctx N) N).toCStorageRef)) := by
    funext store
    rw [joined]
    rfl
  have sequence := Circuit.referenceFiberSum_execute_seq sampler quantumRound state
    finalWeight leftRef rightRef
  have observed := congrArg
    (fun observe : Store (context ctx N) → ℂ =>
      ExecutionState.referenceFiberSum (quantumRound.execute Reference sampled)
        (fun entry _ => observe entry.1) leftRef rightRef) finalWeights
  have measured := NativeStorage.round_referenceFiberSum_input (sampledContext ctx N) N
    sampledWires parameter sourceInput sampled
      (Sampler.Retained.samplerRetained_seeded source _ state seeded)
    jointWeight leftRef rightRef
  have sampledLaw := Sampler.Retained.samplerRetained_reference_input source input state
    (fun old selected drawn => NativeQuantum.readoutWeight selected
      (fun outcome => weight old drawn selected (.bits outcome))) leftRef rightRef
  refine sequence.trans (observed.trans (measured.trans (sampledLaw.trans ?_)))
  apply congrArg
    (fun observe : Store ctx × History → ctx.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe leftRef rightRef)
  funext entry _
  apply Finset.sum_congr rfl
  intro drawn _
  exact congrArg
    (fun coefficient : ℂ => (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * coefficient)
    (NativeQuantum.readoutWeight_source source drawn
      (fun outcome => weight (entry.1.read input) (.bits (Sampler.PackedSample.storedBits drawn))
        (parameterValue source drawn) (.bits outcome)))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeIteration
