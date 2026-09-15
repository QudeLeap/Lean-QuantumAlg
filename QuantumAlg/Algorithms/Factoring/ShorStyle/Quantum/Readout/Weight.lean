/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.Born

/-!
# Weighted phase readout of the actual compiled Shor member

This scalar is computed from the actual program's seed amplitudes. Its
coordinate transport preserves the complete physical basis. For the parameter
produced by one actual source draw, finite phase fibers identify it with the
original sampled Born law, including arbitrary complex result weights.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical

noncomputable section

namespace NativeQuantum

/-- A finite mathematical observation of the existing actual program's seed amplitudes. -/
def readoutWeight {N : Nat} (parameter : (ParameterShape (modulusBits N)).Value)
    (weight : OrderFinding.Outcome (phaseBits N) → ℂ) : ℂ :=
  ∑ basis : Fin (2 ^ totalQubits N),
    weight ((OrderFinding.measurement (phaseBits N)
      (modulusBits N + modulusBits N)).readout basis) *
      (((‖(program parameter).applyNormalized
        (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N)) basis‖ ^ 2 : ℝ) : ℂ))

/-- The weighted source law is derived from the same actual compiled member and seed. -/
theorem readoutWeight_source {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (weight : OrderFinding.Outcome (phaseBits N) → ℂ) :
    readoutWeight (parameterValue input sample) weight =
      ∑ outcome : OrderFinding.Outcome (phaseBits N),
        weight outcome * ((sourceSampleOutcomePMF input sample outcome).toReal : ℂ) := by
  classical
  let read := (OrderFinding.measurement (phaseBits N)
    (modulusBits N + modulusBits N)).readout
  let amplitudeWeight := fun basis : Fin (2 ^ totalQubits N) =>
    ‖(program (parameterValue input sample)).applyNormalized
      (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N)) basis‖ ^ 2
  have partition : readoutWeight (parameterValue input sample) weight =
      ∑ outcome : OrderFinding.Outcome (phaseBits N), weight outcome *
        ((∑ basis : Fin (2 ^ totalQubits N),
          if read basis = outcome then amplitudeWeight basis else 0 : ℝ) : ℂ) := by
    change (∑ basis : Fin (2 ^ totalQubits N),
      weight (read basis) * (amplitudeWeight basis : ℂ)) = _
    simp only [Complex.ofReal_sum, Complex.ofReal_zero, apply_ite, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro basis _
    simp only [mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine partition.trans ?_
  apply Finset.sum_congr rfl
  intro outcome _
  exact congrArg (fun probability : ℝ => weight outcome * (probability : ℂ))
    (program_outcome_weight input sample outcome)

end NativeQuantum

namespace NativePlacement

/-- The actual wire correspondence leaves every weighted phase-amplitude sum unchanged. -/
theorem readoutWeight_coordinates {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)
    (parameter : (ParameterShape (modulusBits N)).Value)
    (weight : OrderFinding.Outcome (phaseBits N) → ℂ) :
    (∑ basis : ctx.register.Index,
      weight ((OrderFinding.measurement (phaseBits N) (modulusBits N + modulusBits N)).readout
        (basisEquiv N sameWires basis)) *
        (((‖(NativeQuantum.program parameter).applyNormalized
          (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N))
            (NativeQuantum.seedLabel N)) (basisEquiv N sameWires basis)‖ ^ 2 : ℝ) : ℂ))) =
      NativeQuantum.readoutWeight parameter weight :=
  (basisEquiv N sameWires).sum_comp
    (fun basis =>
      weight ((OrderFinding.measurement (phaseBits N)
        (modulusBits N + modulusBits N)).readout basis) *
        (((‖(NativeQuantum.program parameter).applyNormalized
          (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N))
            (NativeQuantum.seedLabel N)) basis‖ ^ 2 : ℝ) : ℂ)))

end NativePlacement

end

end QuantumAlg.Factoring.ShorStyle.Canonical
