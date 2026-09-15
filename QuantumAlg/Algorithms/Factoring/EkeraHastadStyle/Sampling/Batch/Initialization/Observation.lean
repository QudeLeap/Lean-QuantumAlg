/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program
import all QuantumAlg.Core.Execution.Preparation.Observation
import all QuantumAlg.Core.Execution.Measurement.Cells.Observation

/-!
# The actual first initialization preserves the sampler's reference observations

The single owned-bank preparation and actual finite-cell allocations retain
every earlier structural sampler input and its full reference correlations.
Consequently the ready bank's weighted parameter/source observation is exactly
that of the actual sampler execution before preparation. No independently
chosen sample, distribution or quantum state is substituted.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open ShortDLP.CompiledMAU
open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem measurement_lift_product {ctx : RuntimeCtx .quantum} {left right : CShape}
    (first : CInputRef ctx left) (second : CInputRef ctx right) (dimension : ℕ+) (count : Nat) :
    MeasurementCells.liftInput dimension (.product first second) count =
      .product (MeasurementCells.liftInput dimension first count)
        (MeasurementCells.liftInput dimension second count) := by
  induction count with
  | zero => rfl
  | succ count induction =>
      exact congrArg
        (fun input :
            CInputRef (MeasurementCells.context ctx dimension count) (.product left right) =>
          input.underRetained (MeasurementCells.context ctx dimension count).canonicalFreshKey
            (.finite dimension)
            (MeasurementCells.context ctx dimension count).canonicalFreshKey_fresh)
        induction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- A joint sampled operand stays the product of its actual separately lifted structural inputs. -/
theorem nativeBatch_readyInput_product {left right : CShape}
    (first : CInputRef (sampledContext base N) left)
    (second : CInputRef (sampledContext base N) right) :
    readyInput base noQuantum N (.product first second) =
      .product (readyInput base noQuantum N first) (readyInput base noQuantum N second) :=
  measurement_lift_product (bankInput base noQuantum N first) (bankInput base noQuantum N second)
    2 (measurementBits N)

/-- The one actual owned-bank preparation preserves the complete sampled-input reference weight. -/
theorem nativeBatch_prepare_reference_input {shape : CShape}
    (input : CInputRef (sampledContext base N) shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sampledContext base N) Reference History) (weight : shape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((RuntimeBank.prepare (sampledContext base N)
          (nativeBatch_sampled_noQuantum base noQuantum N)
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N).execute Reference state)
        (fun entry _ => weight (entry.1.read (bankInput base noQuantum N input)))
        leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef :=
  Circuit.referenceFiberSum_execute_prepare_input input (sampledContext base N).canonicalFreshKey
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N))
    (sampledContext base N).canonicalFreshKey_fresh
    (RuntimeBank.allocationDisjoint (sampledContext base N)
      (nativeBatch_sampled_noQuantum base noQuantum N)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N))
    (seedPreparation (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)
    state weight leftRef rightRef

/-- Ready-bank observations equal those of the same actual sampler execution before preparation. -/
theorem nativeBatch_initialize_reference_input {shape : CShape}
    (input : CInputRef (sampledContext base N) shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (weight : shape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((initializeBank base noQuantum N).execute Reference state)
        (fun entry _ => weight (entry.1.read (readyInput base noQuantum N input)))
        leftRef rightRef =
      ExecutionState.referenceFiberSum
        ((ShorStyle.Canonical.Sampler.Retained.circuit base N).execute Reference state)
        (fun entry _ => weight (entry.1.read input)) leftRef rightRef := by
  have allocated := (Circuit.referenceFiberSum_execute_seq (sampleAndPrepare base noQuantum N)
    (MeasurementCells.allocate (bankContext base noQuantum N) 2 (measurementBits N)) state
    (fun store => weight (store.read (readyInput base noQuantum N input))) leftRef rightRef).trans
    (MeasurementCells.allocate_referenceFiberSum_input (bankInput base noQuantum N input)
      2 (measurementBits N) ((sampleAndPrepare base noQuantum N).execute Reference state)
      weight leftRef rightRef)
  have prepared := (Circuit.referenceFiberSum_execute_seq
    (ShorStyle.Canonical.Sampler.Retained.circuit base N)
    (RuntimeBank.prepare (sampledContext base N)
      (nativeBatch_sampled_noQuantum base noQuantum N)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N) state
    (fun store => weight (store.read (bankInput base noQuantum N input))) leftRef rightRef).trans
    (nativeBatch_prepare_reference_input base noQuantum N input
      ((ShorStyle.Canonical.Sampler.Retained.circuit base N).execute Reference state)
      weight leftRef rightRef)
  exact allocated.trans prepared

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
