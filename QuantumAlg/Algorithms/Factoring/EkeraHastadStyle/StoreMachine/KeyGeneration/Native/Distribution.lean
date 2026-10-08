/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.KeyGeneration.Specification

/-!
# The original uniform key average of actual finite retry outputs

The existing key generator draws ordered distinct odd primes of the same
exact width and requires their product to have twice that width. Each
branch executes the existing finite run with only its public modulus.
The pair labels and natural factor observation belong to the mathematical
average, not to the circuit's complete typed optional-word output.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeKeyGeneration

noncomputable section

open Execution ShortDLP.CompiledMAU ClassicalRoutines.FirstAccepted.Direct

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (bitWidth : Nat) (nonempty : Nonempty (RSA.RSAKeyPairBits bitWidth))
    (totalRounds : Nat) {Reference : Register}
    (inputs : RSA.RSAKeyPairBits bitWidth →
      Execution.OracleInput RuntimeRound.model.classicalOracles base Reference)

/-- Theorem-side key averaging observes each actual modulus-only finite run.
The arbitrary input family permits correlations between keys and initial states. -/
def outputDistribution : PMF (Nat × Nat × Option Nat) :=
  (RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
    ((NativeFiniteRetry.run base noQuantum (inputOfKeyPair pair) totalRounds).outputDistribution
      (inputs pair)).map fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output)

/-- The actual key average has the original finite first-success law in every key branch. -/
theorem outputDistribution_eq :
    outputDistribution base noQuantum bitWidth nonempty totalRounds inputs =
      (RSA.RSAKeyGenBits bitWidth nonempty).bind fun pair =>
        (Optional.Distribution.selectedDistribution
          ((sampledBatchOutputPMF (inputOfKeyPair pair)).map
            (LatticeBatchRecoveryOutput.outputValue (N := pair.modulus))) totalRounds).map
          (fun output => (pair.p, pair.q, NativeRetrySelection.decodeFactor output)) := by
  unfold outputDistribution
  apply congrArg (PMF.bind (RSA.RSAKeyGenBits bitWidth nonempty))
  funext pair
  rw [NativeFiniteRetry.run_outputDistribution]

/-- A supported populated observation is one of the primes generated in that same key branch. -/
theorem outputDistribution_some_sound {p q factor : Nat}
    (member : (p, q, some factor) ∈
      (outputDistribution base noQuantum bitWidth nonempty totalRounds inputs).support) :
    factor = p ∨ factor = q := by
  rw [outputDistribution, PMF.mem_support_bind_iff] at member
  rcases member with ⟨pair, _pairMember, outputMember⟩
  rw [PMF.mem_support_map_iff] at outputMember
  rcases outputMember with ⟨output, outputMember, outputEq⟩
  have leftEq : pair.p = p := congrArg Prod.fst outputEq
  have restEq : (pair.q, NativeRetrySelection.decodeFactor output) = (q, some factor) :=
    congrArg Prod.snd outputEq
  have rightEq : pair.q = q := congrArg Prod.fst restEq
  have factorEq : NativeRetrySelection.decodeFactor output = some factor :=
    congrArg Prod.snd restEq
  subst p
  subst q
  cases output with
  | optionNone => cases factorEq
  | optionSome word =>
      have valueEq : word.toNat = factor := Option.some.inj factorEq
      have sound := NativeFiniteRetry.run_some_sound base noQuantum (inputOfKeyPair pair)
        totalRounds (inputs pair) word outputMember
      have declared := (semiprimeOfKeyPair pair).nontrivial_factor_eq_declared
        sound.1 sound.2.1 sound.2.2
      rw [valueEq] at declared
      exact declared

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeKeyGeneration
