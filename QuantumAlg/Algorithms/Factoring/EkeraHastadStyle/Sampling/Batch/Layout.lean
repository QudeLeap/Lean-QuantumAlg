/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Endpoint
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Bank
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Results
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Measurement.Cells.Inputs

/-!
# Actual first-batch storage and owned-bank layout

The real residue sampler runs first and retains its complete parameter,
including any early-factor tag. Only then does one preparation allocate the
owned short-DLP bank. Structural inputs cross this actual allocation without
copying the sampled value. One finite measurement cell per measured wire is
allocated once, and the rounds retain their distinct packed outcomes in order.

This is the first-batch initialization boundary. A later retry must reuse the
existing bank rather than call this preparation again. The source's early
factor selection remains in recovery after the complete quantum batch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open ShortDLP.CompiledMAU
open Execution

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The original source sample and complete parameter are retained before bank preparation. -/
def sampledContext : RuntimeCtx .quantum :=
  ShorStyle.Canonical.Sampler.Retained.context base N

include noQuantum in
/-- The actual sampler preserves the empty quantum boundary used for the first allocation. -/
theorem nativeBatch_sampled_noQuantum : (sampledContext base N).quantumWires = [] :=
  (ShorStyle.Canonical.Sampler.Retained.samplerNative_quantumWires base N).trans noQuantum

/-- The single actual owned bank is added after sampling, with the source widths unchanged. -/
def bankContext : RuntimeCtx .quantum :=
  RuntimeBank.context (sampledContext base N) (nativeBatch_sampled_noQuantum base noQuantum N)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)

/-- Any sampled structural operand is retained beneath the actual owned-layout marker. -/
def bankInput {shape : CShape} (input : CInputRef (sampledContext base N) shape) :
    CInputRef (bankContext base noQuantum N) shape :=
  input.underOwnedLayout (sampledContext base N).canonicalFreshKey
    (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N))
    (sampledContext base N).canonicalFreshKey_fresh
    (RuntimeBank.allocationDisjoint (sampledContext base N)
      (nativeBatch_sampled_noQuantum base noQuantum N)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N))

/-- Finite measurement cells are allocated once around the already prepared bank. -/
def readyContext : RuntimeCtx .quantum :=
  MeasurementCells.context (bankContext base noQuantum N) 2 (measurementBits N)

/-- An existing sampled operand remains structural underneath the shared measurement cells. -/
def readyInput {shape : CShape} (input : CInputRef (sampledContext base N) shape) :
    CInputRef (readyContext base noQuantum N) shape :=
  MeasurementCells.liftInput 2 (bankInput base noQuantum N input) (measurementBits N)

/-- Every member selects its generator from the same actual retained sampler result. -/
def parameter : CInputRef (readyContext base noQuantum N) (ParameterShape N) :=
  readyInput base noQuantum N
    (.storage (ShorStyle.Canonical.Sampler.Retained.parameterRef base N).toCStorageRef)

/-- Each measured source wire writes to its own existing finite classical cell. -/
def cells : Fin (measurementBits N) → CWriteRef (readyContext base noQuantum N) (.finite 2) :=
  MeasurementCells.reference (bankContext base noQuantum N) 2 (measurementBits N)

/-- The ready context contains exactly the single source bank's actual ordered wire records. -/
theorem nativeBatch_ready_wires :
    (readyContext base noQuantum N).quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires :=
  (MeasurementCells.context_quantumWires (bankContext base noQuantum N) 2
    (measurementBits N)).trans
    (RuntimeBank.shortDLP_runtimeBank_quantumWires (sampledContext base N)
      (nativeBatch_sampled_noQuantum base noQuantum N)
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N))

/-- Actual final storage retains all sixteen chronological outcomes and the same bank. -/
def context : RuntimeCtx .quantum :=
  RuntimeResults.context (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (readyContext base noQuantum N) 16

/-- The complete original sampled operand remains readable after every measured round. -/
def finalInput {shape : CShape} (input : CInputRef (sampledContext base N) shape) :
    CInputRef (context base noQuantum N) shape :=
  RuntimeResults.liftInput (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (readyInput base noQuantum N input) 16

/-- The retained parameter used by the later early-factor-first recovery. -/
def finalParameter : CInputRef (context base noQuantum N) (ParameterShape N) :=
  finalInput base noQuantum N
    (.storage (ShorStyle.Canonical.Sampler.Retained.parameterRef base N).toCStorageRef)

/-- The original retained source bits are still available to the independent batch relation. -/
def finalSample :
    CInputRef (context base noQuantum N) (.bits (residueSamplingBits N)) :=
  finalInput base noQuantum N
    (.storage (ShorStyle.Canonical.Sampler.Retained.sampleRef base N).toCStorageRef)

/-- The sixteen actual terminal outcomes, with their original chronological indices. -/
def finalResults :
    CInputRef (context base noQuantum N) (.fixedVector 16 (.bits (measurementBits N))) :=
  RuntimeResults.input (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (readyContext base noQuantum N) 16

/-- The real final context has exactly the same bank; result recording introduces no systems. -/
theorem nativeBatch_context_wires :
    (context base noQuantum N).quantumWires =
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).wires :=
  (RuntimeResults.shortDLP_runtimeResults_wires
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (readyContext base noQuantum N) 16).trans (nativeBatch_ready_wires base noQuantum N)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
