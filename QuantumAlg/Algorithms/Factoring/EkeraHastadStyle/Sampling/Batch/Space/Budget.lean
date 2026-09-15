/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Space
import all QuantumAlg.Core.Execution.Measurement.Cells.Bounds

/-!
# Independent capacity for the actual first batch

The allowance retains every sampler result, one actual quantum bank, every
finite measurement cell, all sixteen packed outcomes and the reset scratch
bit. The sampler's own lexical peak is included as its independent classical
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

private theorem retained_le_sampler (N : Nat) :
    ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N) ≤
      ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) := by
  intro axis
  cases axis with
  | classicalBits =>
      change 18 * modulusBits N + 1 ≤ 27 * modulusBits N + 15
      omega
  | quantumSystems _ => exact Nat.le_refl 0

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

/-- The ready resident frame contains the actual sampler cells, bank and measurement cells. -/
theorem nativeBatch_ready_residentSpace :
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
theorem nativeBatch_ready_auxiliarySpace :
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

private theorem ready_budget (N : Nat) (original : SpacePool .quantum) :
    SpacePool.ofShape (.finite 2) + 16 • SpacePool.ofShape (.bits (measurementBits N)) +
        (measurementBits N • SpacePool.ofShape (.finite 2) +
          (SpacePool.ofQuantumLayout
            (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) +
            (original +
              ShorStyle.Canonical.Sampler.Retained.resultSpace .quantum (modulusBits N)))) ≤
      original + additionalSpace N := by
  intro axis
  have retained := retained_le_sampler N axis
  change SpacePool.ofShape (.finite 2) axis +
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
  calc
    _ ≤ SpacePool.ofShape (.finite 2) axis +
        (16 • SpacePool.ofShape (.bits (measurementBits N))) axis +
        ((measurementBits N • SpacePool.ofShape (.finite 2)) axis +
          (SpacePool.ofQuantumLayout
            (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) axis +
            (original axis +
              ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum
                (modulusBits N) axis))) :=
      Nat.add_le_add (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _)
        (Nat.add_le_add (Nat.le_refl _) (Nat.add_le_add (Nat.le_refl _) retained)))
    _ = _ := by omega

/-- All actual round results and the scratch bit fit the independent resident allowance. -/
theorem nativeBatch_rounds_resident_budget :
    SpacePool.ofShape (.finite 2) + 16 • SpacePool.ofShape (.bits (measurementBits N)) +
        (readyContext base noQuantum N).residentSpace ≤
      base.residentSpace + additionalSpace N := by
  rw [nativeBatch_ready_residentSpace]
  exact ready_budget N base.residentSpace

/-- Their actual auxiliary roles fit the same independent allowance. -/
theorem nativeBatch_rounds_auxiliary_budget :
    SpacePool.ofShape (.finite 2) + 16 • SpacePool.ofShape (.bits (measurementBits N)) +
        (readyContext base noQuantum N).auxiliarySpace ≤
      base.auxiliarySpace + additionalSpace N := by
  rw [nativeBatch_ready_auxiliarySpace]
  exact ready_budget N base.auxiliarySpace

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
