/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Readout
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Iteration.Seed
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.PackedSample
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Weights
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Reference.Observation
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Joint source law of the actual finite Shor batch

Induction follows the actual sequence and its evolving retained context. The
first actual round keeps the previous input jointly with its new tuple and
the reference; the real reset supplies the next round's seed. The complete
stored vector therefore has the original repeated source law, including its
joint correlation with the initial classical input and every reference entry.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeBatch

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem source_cons {N : Nat} (source : Input N) (count : Nat)
    (weight : (Fin (count + 1) → (NativeIteration.resultShape N).Value) → ℂ) :
    (∑ sample : Fin (2 ^ residueSamplingBits N),
      (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
        ∑ outcome : OrderFinding.Outcome (phaseBits N),
          SourceWeights.batch source count
            (fun tail => weight
              (Fin.cons
                (.product (.bits (Sampler.PackedSample.storedBits sample))
                  (.product (parameterValue source sample) (.bits outcome)))
                (fun index => sourceValue source (tail index)))) *
            ((sourceSampleOutcomePMF source sample outcome).toReal : ℂ)) =
      SourceWeights.batch source (count + 1)
        (fun outcomes => weight (fun index => sourceValue source (outcomes index))) := by
  conv_rhs => unfold SourceWeights.batch SourceWeights.one
  apply Finset.sum_congr rfl
  intro sample _
  apply congrArg (fun coefficient : ℂ =>
    (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) * coefficient)
  apply Finset.sum_congr rfl
  intro outcome _
  apply congrArg (fun coefficient : ℂ =>
    coefficient * ((sourceSampleOutcomePMF source sample outcome).toReal : ℂ))
  apply congrArg (SourceWeights.batch source count)
  funext tail
  exact congrArg weight
    (Fin.comp_cons (sourceValue source) (⟨sample, outcome⟩ : SourceOutcome N) tail).symm

/-- The actual stored vector has the original ordered source law with its whole incoming frame. -/
theorem code_referenceFiberSum_input {N : Nat} (source : Input N) (count : Nat)
    {ctx : RuntimeCtx .quantum}
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    {shape : CShape} (input : CInputRef ctx shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) state)
    (weight : shape.Value → (Fin count → (NativeIteration.resultShape N).Value) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum ((code ctx N sameWires count).execute Reference state)
        (fun entry _ => weight (entry.1.read (liftInput N input count))
          (fun index => entry.1.read (resultInput ctx N count index))) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => SourceWeights.batch source count
          (fun outcomes => weight (entry.1.read input)
            (fun index => sourceValue source (outcomes index)))) leftRef rightRef := by
  induction count generalizing ctx History shape with
  | zero =>
      let finalWeight := fun store : Store ctx => weight (store.read input)
        (fun index => store.read (resultInput ctx N 0 index))
      have executed := congrArg
        (fun output : State ctx Reference (History × Unit) =>
          ExecutionState.referenceFiberSum output (fun entry _ => finalWeight entry.1)
            leftRef rightRef)
        (Circuit.execute_id_mapClassical Reference state)
      have pushed := ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2, ())))
        (fun entry _ => finalWeight entry.1) leftRef rightRef
      refine executed.trans (pushed.trans ?_)
      apply congrArg
        (fun observe : Store ctx × History → ctx.register.Index → ℂ =>
          ExecutionState.referenceFiberSum state observe leftRef rightRef)
      funext entry _
      apply congrArg (weight (entry.1.read input))
      funext index
      exact Fin.elim0 index
  | succ count induction =>
      let first := NativeIteration.code ctx N sameWires
      let nextWires := (NativeIteration.quantumWires ctx N).trans sameWires
      let rest := code (NativeIteration.context ctx N) N nextWires count
      let nextState := first.execute Reference state
      let earlier := NativeIteration.liftInput N input
      let firstTuple := CInputRef.product (NativeIteration.sampleInput ctx N)
        (.product (NativeIteration.parameterInput ctx N) (NativeIteration.phaseInput ctx N))
      let joinedInput := CInputRef.product earlier firstTuple
      let tailWeight : (CShape.product shape (NativeIteration.resultShape N)).Value →
          (Fin count → (NativeIteration.resultShape N).Value) → ℂ :=
        fun joined results => weight joined.first (Fin.cons joined.second results)
      let finalWeight := fun store : Store (context ctx N (count + 1)) =>
        weight (store.read (liftInput N input (count + 1)))
          (fun index => store.read (resultInput ctx N (count + 1) index))
      have finalWeights : finalWeight =
          fun store : Store (context (NativeIteration.context ctx N) N count) =>
            tailWeight (store.read (liftInput N joinedInput count))
              (fun index => store.read
                (resultInput (NativeIteration.context ctx N) N count index)) := by
        funext store
        change weight (store.read (liftInput N earlier count))
            (fun index => store.read (resultInput ctx N (count + 1) index)) =
          weight (store.read (liftInput N (.product earlier firstTuple) count)).first
            (Fin.cons (store.read (liftInput N (.product earlier firstTuple) count)).second
              (fun index => store.read
                (resultInput (NativeIteration.context ctx N) N count index)))
        rw [liftInput_product]
        exact congrArg (weight (store.read (liftInput N earlier count)))
          (read_resultInput_cons ctx N count store)
      have sequence := Circuit.referenceFiberSum_execute_seq first rest state finalWeight
        leftRef rightRef
      have observed := congrArg
        (fun observe : Store (context (NativeIteration.context ctx N) N count) → ℂ =>
          ExecutionState.referenceFiberSum (rest.execute Reference nextState)
            (fun entry _ => observe entry.1) leftRef rightRef) finalWeights
      have tailLaw := induction nextWires joinedInput nextState
        (NativeIteration.code_seeded N sameWires state) tailWeight
      have firstLaw := NativeIteration.code_referenceFiberSum_input source sameWires input
        state seeded
        (fun old sample parameter phase => SourceWeights.batch source count
          (fun outcomes => weight old
            (Fin.cons (.product sample (.product parameter phase))
              (fun index => sourceValue source (outcomes index))))) leftRef rightRef
      refine sequence.trans (observed.trans (tailLaw.trans (firstLaw.trans ?_)))
      apply congrArg
        (fun observe : Store ctx × History → ctx.register.Index → ℂ =>
          ExecutionState.referenceFiberSum state observe leftRef rightRef)
      funext entry _
      exact source_cons source count (weight (entry.1.read input))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeBatch
