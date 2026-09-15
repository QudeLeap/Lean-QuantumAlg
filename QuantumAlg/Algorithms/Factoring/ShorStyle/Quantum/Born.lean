/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.Amplitude.Source
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Placement
import all QuantumAlg.Core.Measure.RealWeights

/-!
# Original sampled Born weights of the actual Shor bank

The actual compiled member's phase fiber first sums its target and auxiliary
words. The auxiliary has exactly zero value, so the result is the original
source phase probability. The physical wire correspondence transports this
same sum into the runtime register without changing any amplitude or value.
The identities describe weights derived from the actual gate program; the
native measurement and reference-fiber proofs consume them separately.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical

noncomputable section

namespace NativeQuantum

private theorem phase_fiber_sum (phaseWidth targetWidth : Nat)
    (weight : Fin (2 ^ (phaseWidth + targetWidth)) → ℝ) (phase : Fin (2 ^ phaseWidth)) :
    (∑ basis : Fin (2 ^ (phaseWidth + targetWidth)),
      if (OrderFinding.measurement phaseWidth targetWidth).readout basis =
          OrderFinding.measurementOutcome phaseWidth phase then weight basis else 0) =
      ∑ target : Fin (2 ^ targetWidth), weight (prodEquiv (phase, target)) := by
  classical
  rw [← Finset.sum_filter, OrderFinding.BornBridge.orderFindingMeasurement_fiber,
    Finset.sum_map]
  rfl

/-- Every compiled source-sample phase fiber is the original sampled Born probability. -/
theorem program_outcome_weight {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (outcome : OrderFinding.Outcome (phaseBits N)) :
    (∑ basis : Fin (2 ^ totalQubits N),
      if (OrderFinding.measurement (phaseBits N) (modulusBits N + modulusBits N)).readout
          basis = outcome then
        ‖(program (parameterValue input sample)).applyNormalized
          (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N)) basis‖ ^ 2 else 0) =
      (sourceSampleOutcomePMF input sample outcome).toReal := by
  classical
  obtain ⟨phase, rfl⟩ :=
    (OrderFinding.BornBridge.orderFindingMeasurementOutcome_bijective (phaseBits N)).surjective
      outcome
  let weight : Fin (2 ^ (phaseBits N + (modulusBits N + modulusBits N))) → ℝ :=
    fun basis => ‖(program (parameterValue input sample)).applyNormalized
      (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N)) basis‖ ^ 2
  refine (phase_fiber_sum (phaseBits N) (modulusBits N + modulusBits N) weight phase).trans ?_
  have coordinates := (prodEquiv (m := modulusBits N) (n := modulusBits N)).sum_comp
    (fun suffix => weight (prodEquiv (phase, suffix)))
  refine coordinates.symm.trans ?_
  rw [Fintype.sum_prod_type]
  have auxiliary := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun target _ => program_sample_auxiliary_weight input sample phase target)
  refine auxiliary.trans ?_
  have source := TerminalZMeasure.outcomePMF_toReal
    (OrderFinding.measurement (phaseBits N) (modulusBits N))
    (sourceSampleState input sample) (OrderFinding.measurementOutcome (phaseBits N) phase)
  have sourceFiber :
      (∑ basis : Fin (2 ^ (phaseBits N + modulusBits N)),
        if (OrderFinding.measurement (phaseBits N) (modulusBits N)).readout basis =
            OrderFinding.measurementOutcome (phaseBits N) phase then
          ‖(sourceSampleState input sample).normalized basis‖ ^ 2 else 0) =
        ∑ target : Fin (2 ^ modulusBits N),
          ‖(sourceSampleState input sample).normalized (prodEquiv (phase, target))‖ ^ 2 :=
    phase_fiber_sum (phaseBits N) (modulusBits N)
      (fun basis => ‖(sourceSampleState input sample).normalized basis‖ ^ 2) phase
  exact (source.trans sourceFiber).symm

end NativeQuantum

namespace NativePlacement

/-- Each actual physical phase fiber has the same source-sample probability. -/
theorem source_sample_outcome_weight {ctx : RuntimeCtx .quantum} {N : Nat} (input : Input N)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (sample : Fin (2 ^ residueSamplingBits N)) (outcome : OrderFinding.Outcome (phaseBits N)) :
    (∑ basis : ctx.register.Index,
      if (OrderFinding.measurement (phaseBits N) (modulusBits N + modulusBits N)).readout
          (basisEquiv N sameWires basis) = outcome then
        ‖(NativeQuantum.program (parameterValue input sample)).applyNormalized
          (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N))
            (NativeQuantum.seedLabel N)) (basisEquiv N sameWires basis)‖ ^ 2 else 0) =
      (sourceSampleOutcomePMF input sample outcome).toReal := by
  classical
  exact ((basisEquiv N sameWires).sum_comp
    (fun basis =>
      if (OrderFinding.measurement (phaseBits N) (modulusBits N + modulusBits N)).readout
          basis = outcome then
        ‖(NativeQuantum.program (parameterValue input sample)).applyNormalized
          (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N))
            (NativeQuantum.seedLabel N)) basis‖ ^ 2 else 0)).trans
    (NativeQuantum.program_outcome_weight input sample outcome)

end NativePlacement

end

end QuantumAlg.Factoring.ShorStyle.Canonical
