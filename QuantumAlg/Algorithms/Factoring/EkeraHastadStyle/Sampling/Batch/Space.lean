/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Space.Budget
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Repetition.Space

/-!
# Every actually live first-batch frame fits the independent allowance

The proof follows the real sampler, zero allocation and X loading on the one
owned bank, actual measurement-cell allocation and the sixteen-round trace.
All retained outcomes remain counted. The reset workspace is counted while
live, and the same bank supplies the only additional quantum systems.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

open Execution
open ShortDLP.CompiledMAU

private theorem sampler_budget (N : Nat) (original : SpacePool .quantum) :
    original + ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) ≤
      original + additionalSpace N := by
  intro axis
  change original axis +
      ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) axis ≤
    original axis +
      (ShorStyle.Canonical.Sampler.Retained.additionalSpace .quantum (modulusBits N) axis +
        SpacePool.ofQuantumLayout
          (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) axis +
        (measurementBits N • SpacePool.ofShape (.finite 2)) axis +
        (16 • SpacePool.ofShape (.bits (measurementBits N))) axis +
        SpacePool.ofShape (.finite 2) axis)
  omega

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

private theorem ready_bounds :
    (readyContext base noQuantum N).residentSpace ≤ base.residentSpace + additionalSpace N ∧
      (readyContext base noQuantum N).auxiliarySpace ≤
        base.auxiliarySpace + additionalSpace N :=
  ⟨(show (readyContext base noQuantum N).residentSpace ≤
        SpacePool.ofShape (.finite 2) + 16 • SpacePool.ofShape (.bits (measurementBits N)) +
          (readyContext base noQuantum N).residentSpace from
      fun _ => Nat.le_add_left _ _).trans (nativeBatch_rounds_resident_budget base noQuantum N),
    (show (readyContext base noQuantum N).auxiliarySpace ≤
        SpacePool.ofShape (.finite 2) + 16 • SpacePool.ofShape (.bits (measurementBits N)) +
          (readyContext base noQuantum N).auxiliarySpace from
      fun _ => Nat.le_add_left _ _).trans (nativeBatch_rounds_auxiliary_budget base noQuantum N)⟩

private theorem bank_bounds :
    (bankContext base noQuantum N).residentSpace ≤ base.residentSpace + additionalSpace N ∧
      (bankContext base noQuantum N).auxiliarySpace ≤
        base.auxiliarySpace + additionalSpace N := by
  have resident : (bankContext base noQuantum N).residentSpace ≤
      (readyContext base noQuantum N).residentSpace :=
    (show (bankContext base noQuantum N).residentSpace ≤
        measurementBits N • SpacePool.ofShape (.finite 2) +
          (bankContext base noQuantum N).residentSpace from
      fun _ => Nat.le_add_left _ _).trans_eq
      (MeasurementCells.context_residentSpace (bankContext base noQuantum N)
        2 (measurementBits N)).symm
  have auxiliary : (bankContext base noQuantum N).auxiliarySpace ≤
      (readyContext base noQuantum N).auxiliarySpace :=
    (show (bankContext base noQuantum N).auxiliarySpace ≤
        measurementBits N • SpacePool.ofShape (.finite 2) +
          (bankContext base noQuantum N).auxiliarySpace from
      fun _ => Nat.le_add_left _ _).trans_eq
      (MeasurementCells.context_auxiliarySpace (bankContext base noQuantum N)
        2 (measurementBits N)).symm
  exact ⟨resident.trans (ready_bounds base noQuantum N).1,
    auxiliary.trans (ready_bounds base noQuantum N).2⟩

include noQuantum in
private theorem sampled_bounds :
    (sampledContext base N).residentSpace ≤ base.residentSpace + additionalSpace N ∧
      (sampledContext base N).auxiliarySpace ≤ base.auxiliarySpace + additionalSpace N := by
  have resident : (sampledContext base N).residentSpace ≤
      (bankContext base noQuantum N).residentSpace :=
    (show (sampledContext base N).residentSpace ≤
        SpacePool.ofQuantumLayout
          (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) +
            (sampledContext base N).residentSpace from
      fun _ => Nat.le_add_left _ _).trans_eq
      (RuntimeBank.shortDLP_runtimeBank_resident (sampledContext base N)
        (nativeBatch_sampled_noQuantum base noQuantum N)
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).symm
  have auxiliary : (sampledContext base N).auxiliarySpace ≤
      (bankContext base noQuantum N).auxiliarySpace :=
    (show (sampledContext base N).auxiliarySpace ≤
        SpacePool.ofQuantumLayout
          (runtimeLayout (shortLogBits N) (tradeoffBits N) (arithmeticBits N)) +
            (sampledContext base N).auxiliarySpace from
      fun _ => Nat.le_add_left _ _).trans_eq
      (RuntimeBank.shortDLP_runtimeBank_auxiliary (sampledContext base N)
        (nativeBatch_sampled_noQuantum base noQuantum N)
        (shortLogBits N) (tradeoffBits N) (arithmeticBits N)).symm
  exact ⟨resident.trans (bank_bounds base noQuantum N).1,
    auxiliary.trans (bank_bounds base noQuantum N).2⟩

private theorem visited_bounds (path : (code base noQuantum N).Path)
    (frame : RuntimeCtx .quantum)
    (present : frame ∈ (code base noQuantum N).visitedContexts path) :
    frame.residentSpace ≤ base.residentSpace + additionalSpace N ∧
      frame.auxiliarySpace ≤ base.auxiliarySpace + additionalSpace N := by
  let sampler := ShorStyle.Canonical.Sampler.Retained.circuit
    (model := RuntimeRound.model) base N
  let allocate := MeasurementCells.allocate (model := RuntimeRound.model)
    (bankContext base noQuantum N) 2 (measurementBits N)
  change frame ∈ List.append (α := RuntimeCtx .quantum)
    (List.append (α := RuntimeCtx .quantum)
      (List.append (α := RuntimeCtx .quantum) (sampler.visitedContexts path.1.1.1)
        [sampledContext base N, bankContext base noQuantum N, bankContext base noQuantum N])
      (allocate.visitedContexts path.1.2))
    ((rounds base noQuantum N).visitedContexts path.2) at present
  simp only [List.append_eq, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with ((sampled | (rfl | rfl | rfl)) | allocated) | repeated
  · exact ⟨((Circuit.residentSpace_le_peak_of_visited sampler path.1.1.1 frame sampled).trans
        (ShorStyle.Canonical.Sampler.Retained.samplerRetained_resident_le
          (model := RuntimeRound.model) base N path.1.1.1)).trans
          (sampler_budget N base.residentSpace),
      ((Circuit.auxiliarySpace_le_peak_of_visited sampler path.1.1.1 frame sampled).trans
        (ShorStyle.Canonical.Sampler.Retained.samplerRetained_auxiliary_le
          (model := RuntimeRound.model) base N path.1.1.1)).trans
          (sampler_budget N base.auxiliarySpace)⟩
  · exact sampled_bounds base noQuantum N
  · exact bank_bounds base noQuantum N
  · exact bank_bounds base noQuantum N
  · exact ⟨((Circuit.residentSpace_le_peak_of_visited allocate path.1.2 frame allocated).trans
        (MeasurementCells.allocate_peakResidentSpace (model := RuntimeRound.model)
          (bankContext base noQuantum N)
          2 (measurementBits N) path.1.2)).trans (ready_bounds base noQuantum N).1,
      ((Circuit.auxiliarySpace_le_peak_of_visited allocate path.1.2 frame allocated).trans
        (MeasurementCells.allocate_peakAuxiliarySpace (model := RuntimeRound.model)
          (bankContext base noQuantum N)
          2 (measurementBits N) path.1.2)).trans (ready_bounds base noQuantum N).2⟩
  · exact ⟨((Circuit.residentSpace_le_peak_of_visited (rounds base noQuantum N)
        path.2 frame repeated).trans
        (RuntimeRepetition.shortDLP_runtimeRepetition_resident_le
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
          (parameterUnit (N := N)) (parameterTarget (N := N))
          (readyContext base noQuantum N) (nativeBatch_ready_wires base noQuantum N)
          (parameter base noQuantum N) (cells base noQuantum N) 16 path.2)).trans
            (nativeBatch_rounds_resident_budget base noQuantum N),
      ((Circuit.auxiliarySpace_le_peak_of_visited (rounds base noQuantum N)
        path.2 frame repeated).trans
        (RuntimeRepetition.shortDLP_runtimeRepetition_auxiliary_le
          (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N
          (parameterUnit (N := N)) (parameterTarget (N := N))
          (readyContext base noQuantum N) (nativeBatch_ready_wires base noQuantum N)
          (parameter base noQuantum N) (cells base noQuantum N) 16 path.2)).trans
            (nativeBatch_rounds_auxiliary_budget base noQuantum N)⟩

/-- Every actual resident frame fits the independent first-batch allowance. -/
theorem nativeBatch_peakResidentSpace_le (path : (code base noQuantum N).Path) :
    (code base noQuantum N).peakResidentSpace path ≤ base.residentSpace + additionalSpace N :=
  Circuit.peakResidentSpace_le_of_visited _ path _
    (fun frame present => (visited_bounds base noQuantum N path frame present).1)

/-- All actual owned and retained auxiliary roles fit their independent allowance. -/
theorem nativeBatch_peakAuxiliarySpace_le (path : (code base noQuantum N).Path) :
    (code base noQuantum N).peakAuxiliarySpace path ≤ base.auxiliarySpace + additionalSpace N :=
  Circuit.peakAuxiliarySpace_le_of_visited _ path _
    (fun frame present => (visited_bounds base noQuantum N path frame present).2)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
