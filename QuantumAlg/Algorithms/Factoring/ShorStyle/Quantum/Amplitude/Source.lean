/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.Amplitude
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Distribution

/-!
# The unchanged sampled Shor source in the compiled bank

The source sampler's stored base is precisely the modular unit selected by
the actual member. Its original phase and target amplitudes therefore agree
with the compiled member, whose sole arithmetic auxiliary word is zero.
The equality applies to every source sample on the original modulus domain.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum

noncomputable section

/-- The original sampled member has the same exact modular-unit source amplitude. -/
theorem sourceSample_amplitude {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (phase : Fin (2 ^ phaseBits N))
    (target : Fin (2 ^ modulusBits N)) :
    (sourceSampleState input sample).normalized (prodEquiv (phase, target)) =
      OrderFinding.BornBridge.circuitSourceAmplitude
        (sourceAccess input (parameterValue input sample)) phase target := by
  let access : OrderFinding.ModExpOracleAccess N (parameterValue input sample).first.toNat
      (phaseBits N) (modulusBits N) :=
    ⟨input.modulus_pos, input.register_fits⟩
  have actual := OrderFinding.BornBridge.orderFindingCircuit_amplitude access phase target
  refine actual.trans ?_
  have targets (exponent : Fin (2 ^ phaseBits N)) :
      OrderFinding.modExpOracleTarget (sourceAccess input (parameterValue input sample))
          exponent 0 = OrderFinding.modExpOracleTarget access exponent 0 := by
    apply Fin.ext
    exact congrArg (fun base : Nat => Nat.xor 0 (base ^ exponent.val % N))
      (selectedBase_parameterValue input sample)
  simp only [OrderFinding.BornBridge.circuitSourceAmplitude, targets]

/-- Every compiled sampled amplitude is the original source amplitude with a zero auxiliary. -/
theorem program_sample_amplitude {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (phase : Fin (2 ^ phaseBits N))
    (target work : Fin (2 ^ modulusBits N)) :
    (program (parameterValue input sample)).applyNormalized
      (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N))
        (prodEquiv (phase, prodEquiv (target, work))) =
      if work = 0 then (sourceSampleState input sample).normalized (prodEquiv (phase, target))
      else 0 :=
  (program_amplitude input (parameterValue input sample) phase target work).trans
    (congrArg (fun amplitude : ℂ => if work = 0 then amplitude else 0)
      (sourceSample_amplitude input sample phase target).symm)

/-- Summing the actual auxiliary word retains precisely the original source Born weight. -/
theorem program_sample_auxiliary_weight {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (phase : Fin (2 ^ phaseBits N))
    (target : Fin (2 ^ modulusBits N)) :
    (∑ work : Fin (2 ^ modulusBits N),
      ‖(program (parameterValue input sample)).applyNormalized
        (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N))
          (prodEquiv (phase, prodEquiv (target, work)))‖ ^ 2) =
      ‖(sourceSampleState input sample).normalized (prodEquiv (phase, target))‖ ^ 2 := by
  classical
  have entries (work : Fin (2 ^ modulusBits N)) :
      ‖(program (parameterValue input sample)).applyNormalized
        (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N))
          (prodEquiv (phase, prodEquiv (target, work)))‖ ^ 2 =
        if work = 0 then
          ‖(sourceSampleState input sample).normalized (prodEquiv (phase, target))‖ ^ 2 else 0 := by
    rw [program_sample_amplitude input sample phase target work]
    by_cases zero : work = 0
    · rw [if_pos zero, if_pos zero]
    · rw [if_neg zero, if_neg zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  exact (Finset.sum_congr rfl fun work _ => entries work).trans
    (by simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true])

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum
