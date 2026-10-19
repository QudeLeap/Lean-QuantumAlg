/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Frame

/-!
# A fresh source batch on an existing quantum bank and measurement cells

The original bank and its finite measurement cells remain in the caller
context. Two fresh classical source cells retain the next uniform sample
and full parameter. Sixteen new packed outcomes preserve chronological
order. Every earlier caller entry remains live and explicitly accounted for.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse

noncomputable section

open Execution ShortDLP.CompiledMAU

variable (base : RuntimeCtx .quantum) (N : Nat)

/-- A new complete source sample is retained around the same existing bank. -/
def sampledContext : RuntimeCtx .quantum :=
  ShorStyle.Canonical.Sampler.Retained.context base N

/-- An old writable cell crosses only the two actual classical source allocations. -/
def sampledWrite {shape : CShape} (input : CWriteRef base shape) :
    CWriteRef (sampledContext base N) shape :=
  (input.underRetained base.canonicalFreshKey (.bits (residueSamplingBits N))
    base.canonicalFreshKey_fresh).underRetained
      (ShorStyle.Canonical.Sampler.Retained.sampleContext base N).canonicalFreshKey
      (ParameterShape N)
      (ShorStyle.Canonical.Sampler.Retained.sampleContext base N).canonicalFreshKey_fresh

/-- The same original finite measurement cells are reused by the later rounds. -/
def cells (original : Fin (measurementBits N) → CWriteRef base (.finite 2)) :
    Fin (measurementBits N) → CWriteRef (sampledContext base N) (.finite 2) :=
  fun index => sampledWrite base N (original index)

/-- Actual member dispatch reads the newly computed complete source parameter. -/
def parameter : CInputRef (sampledContext base N) (ParameterShape N) :=
  .storage (ShorStyle.Canonical.Sampler.Retained.parameterRef base N).toCStorageRef

/-- The complete sampled context has exactly the earlier bank's ordered physical wires. -/
lemma nativeBatchReuse_sampled_wires
    (sameWires : base.quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires) :
    (sampledContext base N).quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires :=
  (ShorStyle.Canonical.Sampler.Retained.samplerNative_quantumWires base N).trans sameWires

/-- Sixteen chronological packed results are retained around that same existing bank. -/
def context : RuntimeCtx .quantum :=
  RuntimeResults.context (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (sampledContext base N) 16

/-- Any structural source operand stays readable after all sixteen real rounds. -/
def finalInput {shape : CShape} (input : CInputRef (sampledContext base N) shape) :
    CInputRef (context base N) shape :=
  RuntimeResults.liftInput (shortLogBits N) (tradeoffBits N) (arithmeticBits N) input 16

/-- A caller input crosses the source allocations and all packed-result allocations. -/
def callerInput {shape : CShape} (input : CInputRef base shape) :
    CInputRef (context base N) shape :=
  finalInput base N (ShorStyle.Canonical.Sampler.Retained.liftInput (N := N) input)

/-- The actual new uniform source remains present in the final store. -/
def finalSample : CInputRef (context base N) (.bits (residueSamplingBits N)) :=
  finalInput base N
    (.storage (ShorStyle.Canonical.Sampler.Retained.sampleRef base N).toCStorageRef)

/-- The complete parameter, including its early-factor field, remains present. -/
def finalParameter : CInputRef (context base N) (ParameterShape N) :=
  finalInput base N (parameter base N)

/-- The source-order vector is read from the sixteen actual retained outcome cells. -/
def finalResults :
    CInputRef (context base N) (.fixedVector 16 (.bits (measurementBits N))) :=
  RuntimeResults.input (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (sampledContext base N) 16

/-- Repetition introduces no quantum systems and leaves the original wire identities intact. -/
lemma nativeBatchReuse_context_wires
    (sameWires : base.quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires) :
    (context base N).quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires :=
  (RuntimeResults.shortDLP_runtimeResults_wires
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N) (sampledContext base N) 16).trans
      (nativeBatchReuse_sampled_wires base N sameWires)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatchReuse
