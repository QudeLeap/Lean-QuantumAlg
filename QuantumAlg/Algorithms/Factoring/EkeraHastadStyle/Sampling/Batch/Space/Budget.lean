/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Space.Reset
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Space
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds

/-!
# Independent capacity for the actual first batch

The allowance retains every sampler result, one actual quantum bank, every
finite measurement cell, all sixteen packed outcomes and the simultaneous
reset result bank. The sampler's own lexical peak is included as its independent classical
allowance. At quantum coordinates the allowance contains only the one source
layout. No repeated round allocates another bank.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open Execution
open ShortDLP.CompiledMAU

/-- Independent storage allowance, including all real retained cells and the one owned bank. -/
def additionalSpace (N : Nat) : SpacePool .quantum :=
  ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) +
    SpacePool.ofQuantumLayout
      (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) +
    measurementBits N • SpacePool.ofShape (.finite 2) +
    16 • SpacePool.ofShape (.bits (measurementBits N)) +
    SpacePool.ofShape (.finite 2)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The ready resident frame contains the actual sampler cells, bank and measurement cells. -/
lemma nativeBatch_ready_residentSpace :
    (readyContext base noQuantum N).residentSpace =
      measurementBits N • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout
          (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) +
          (base.residentSpace +
            ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N))) := by
  have allocated := MeasurementCells.context_residentSpace (bankContext base noQuantum N)
    2 (measurementBits N)
  have bank := RuntimeBank.shortDLP_runtimeBank_resident (sampledContext base N)
    (nativeBatch_sampled_noQuantum base noQuantum N)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
  have sampled := ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_resident base N
  exact allocated.trans (congrArg
    (fun frame : SpacePool .quantum => measurementBits N • SpacePool.ofShape (.finite 2) + frame)
    (bank.trans (congrArg
      (fun frame : SpacePool .quantum =>
        SpacePool.ofQuantumLayout
          (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) + frame)
      sampled)))

/-- The same real retained cells and owned bank have their full auxiliary roles. -/
lemma nativeBatch_ready_auxiliarySpace :
    (readyContext base noQuantum N).auxiliarySpace =
      measurementBits N • SpacePool.ofShape (.finite 2) +
        (SpacePool.ofQuantumLayout
          (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) +
          (base.auxiliarySpace +
            ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N))) := by
  have allocated := MeasurementCells.context_auxiliarySpace (bankContext base noQuantum N)
    2 (measurementBits N)
  have bank := RuntimeBank.shortDLP_runtimeBank_auxiliary (sampledContext base N)
    (nativeBatch_sampled_noQuantum base noQuantum N)
    (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
  have sampled := ShorStyle.Canonical.Sampler.Retained.samplerRetained_context_auxiliary base N
  exact allocated.trans (congrArg
    (fun frame : SpacePool .quantum => measurementBits N • SpacePool.ofShape (.finite 2) + frame)
    (bank.trans (congrArg
      (fun frame : SpacePool .quantum =>
        SpacePool.ofQuantumLayout
          (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) + frame)
      sampled)))

private lemma ready_budget (N : Nat) (original : SpacePool .quantum) :
    RuntimeRound.resetSpace (shortLogBits N) (tradeoffBits N) (arithmeticBits N) +
      16 • SpacePool.ofShape (.bits (measurementBits N)) +
        (measurementBits N • SpacePool.ofShape (.finite 2) +
          (SpacePool.ofQuantumLayout
            (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) +
            (original +
              ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N)))) ≤
      original + additionalSpace N := by
  intro axis
  have retained := nativeBatch_reset_retained_le_sampler N axis
  change RuntimeRound.resetSpace (shortLogBits N) (tradeoffBits N) (arithmeticBits N) axis +
    ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N) axis ≤
      ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) axis
    at retained
  change RuntimeRound.resetSpace (shortLogBits N) (tradeoffBits N) (arithmeticBits N) axis +
      (16 • SpacePool.ofShape (.bits (measurementBits N))) axis +
      ((measurementBits N • SpacePool.ofShape (.finite 2)) axis +
        (SpacePool.ofQuantumLayout
          (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) axis +
          (original axis +
            ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N) axis))) ≤
    original axis +
      (ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) axis +
        SpacePool.ofQuantumLayout
          (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) axis +
        (measurementBits N • SpacePool.ofShape (.finite 2)) axis +
        (16 • SpacePool.ofShape (.bits (measurementBits N))) axis +
        SpacePool.ofShape (.finite 2) axis)
  omega

/-- All round results and simultaneous reset scratch fit the independent resident allowance. -/
lemma nativeBatch_rounds_resident_budget :
    RuntimeRound.resetSpace (shortLogBits N) (tradeoffBits N) (arithmeticBits N) +
      16 • SpacePool.ofShape (.bits (measurementBits N)) +
        (readyContext base noQuantum N).residentSpace ≤
      base.residentSpace + additionalSpace N := by
  rw [nativeBatch_ready_residentSpace]
  exact ready_budget N base.residentSpace

/-- Their actual auxiliary roles fit the same independent allowance. -/
lemma nativeBatch_rounds_auxiliary_budget :
    RuntimeRound.resetSpace (shortLogBits N) (tradeoffBits N) (arithmeticBits N) +
      16 • SpacePool.ofShape (.bits (measurementBits N)) +
        (readyContext base noQuantum N).auxiliarySpace ≤
      base.auxiliarySpace + additionalSpace N := by
  rw [nativeBatch_ready_auxiliarySpace]
  exact ready_budget N base.auxiliarySpace

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
