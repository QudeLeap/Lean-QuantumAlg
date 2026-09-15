/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.Superposition
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.OracleAgreement
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Quantum.Readout.Action

/-!
# Exact source amplitudes of the actual shared-bank Shor member

The original source phase and target amplitudes are recovered exactly from
the real Hadamard, compiled modular-power and inverse-QFT sequence. The sole
arithmetic auxiliary word is zero. The equality retains complex phases and
all unmeasured coordinates, before any actual Z instruction is executed.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum

noncomputable section

open scoped BigOperators
open Nat.FixedWidth

/-- The original source amplitude is unchanged, with the actual auxiliary word exactly zero. -/
theorem program_amplitude {N : Nat} (input : Input N)
    (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (phase : Fin (2 ^ phaseBits N)) (target work : Fin (2 ^ modulusBits N)) :
    (program parameter).applyNormalized
      (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N))
        (prodEquiv (phase, prodEquiv (target, work))) =
      if work = 0 then
        OrderFinding.BornBridge.circuitSourceAmplitude (sourceAccess input parameter) phase target
      else 0 := by
  classical
  let preparation := OrderFinding.orderFindingPreparationCircuit (phaseBits N)
    (modulusBits N + modulusBits N)
  let power := MAU.Exponentiation.Gidney.program (phaseBits N) (modulusBits N)
    (modulus N) (selectedUnit (N := N) parameter)
  let readout := OrderFinding.orderFindingReadoutCircuit (phaseBits N)
    (modulusBits N + modulusBits N)
  let label := fun exponent : Fin (2 ^ phaseBits N) =>
    (MAU.Exponentiation.Gidney.encoding (phaseBits N) (modulusBits N)).encode
      (exponent, unitResidueWord (modulus N) input.modulus_pos
        (selectedUnit (N := N) parameter ^ exponent.val), 0)
  have prepared := congrArg readout.applyVec (power_after_preparation input parameter)
  have first := UnitaryCircuit.applyVec_seq preparation (power.seq readout)
    (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N)).vec
  have second := UnitaryCircuit.applyVec_seq power readout
    (preparation.applyVec
      (NormalizedVector.ket (R := Qubits (totalQubits N)) (seedLabel N)).vec)
  have distributed :
      readout.applyVec (∑ exponent : Fin (2 ^ phaseBits N),
        WalshHadamard.invSqrtCard (phaseBits N) •
          (NormalizedVector.ket (R := Qubits (totalQubits N)) (label exponent)).vec) =
        ∑ exponent : Fin (2 ^ phaseBits N), WalshHadamard.invSqrtCard (phaseBits N) •
          readout.applyVec
            (NormalizedVector.ket (R := Qubits (totalQubits N)) (label exponent)).vec := by
    refine (circuit_applyVec_sum readout
      (fun exponent : Fin (2 ^ phaseBits N) => WalshHadamard.invSqrtCard (phaseBits N) •
        (NormalizedVector.ket (R := Qubits (totalQubits N)) (label exponent)).vec)).trans ?_
    apply Finset.sum_congr rfl
    intro exponent _present
    exact UnitaryCircuit.applyVec_smul readout _ _
  have point := congrArg
    (fun vector : HilbertVector (Qubits (phaseBits N + (modulusBits N + modulusBits N))) =>
      vector (prodEquiv (phase, prodEquiv (target, work))))
    (first.trans (second.trans (prepared.trans distributed)))
  refine point.trans ?_
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul]
  have entries : ∀ exponent : Fin (2 ^ phaseBits N),
      readout.applyVec (NormalizedVector.ket (R := Qubits (totalQubits N)) (label exponent)).vec
        (prodEquiv (phase, prodEquiv (target, work))) =
      star (invSqrtN (phaseBits N) * ω (phaseBits N) ^ (exponent.val * phase.val)) *
        if target = OrderFinding.modExpOracleTarget (sourceAccess input parameter) exponent 0 ∧
          work = 0 then 1 else 0 := by
    intro exponent
    have actual := readout_basis_entry N phase exponent (prodEquiv (target, work))
      (prodEquiv (unitResidueWord (modulus N) input.modulus_pos
        (selectedUnit (N := N) parameter ^ exponent.val), (0 : Fin (2 ^ modulusBits N))))
    refine actual.trans ?_
    rw [power_word_eq_target input parameter exponent]
    simp only [EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  simp only [entries]
  by_cases empty : work = 0
  · rw [if_pos empty, OrderFinding.BornBridge.circuitSourceAmplitude]
    apply Finset.sum_congr rfl
    intro exponent _present
    by_cases targetEqual :
        target = OrderFinding.modExpOracleTarget (sourceAccess input parameter) exponent 0
    · simp only [targetEqual, empty, and_self, if_true, mul_one]
      exact mul_comm _ _
    · simp only [targetEqual, false_and, if_false, mul_zero]
  · rw [if_neg empty]
    simp only [empty, and_false, if_false, mul_zero, Finset.sum_const_zero]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeQuantum
