/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Batch.Values
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.BornProbability
import all QuantumAlg.Util.PMF
import Mathlib.Probability.Distributions.Uniform

/-!
# Original Ekerå--Håstad same-source batch distributions

One uniform source integer determines the prepared residue and complete
parameter. Its selected short-DLP Born law supplies sixteen independent
terminal values, followed by the unchanged first-success scan of all 120
recovery pairs. These are pure mathematical distributions and recovery
values; an executable endpoint must separately prove its actual output law.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical

noncomputable section

/-- The original selected member's mathematical Born law. Invalid RSA moduli
have a total fallback; certified inputs always select the source Born branch. -/
def selectedOutcomePMF {N : Nat} (parameter : (ParameterShape N).Value) :
    PMF (Fin (measurementBits N) → Bool) :=
  if admissible : 1 < N ∧ N < 2 ^ arithmeticBits N then
    (ShortDLP.measurement (ShortDLP.CompiledMAU.registerParameters
      (shortLogBits N) (tradeoffBits N) (arithmeticBits N))).outcomePMF
      (ShortDLP.BornProbability.evolvedState
        (ShortDLP.CompiledMAU.unitEncoding (arithmeticBits N) N
          admissible.1 admissible.2)
        (parameterUnit parameter) (parameterTarget parameter))
  else PMF.pure (fun _ => false)

/-- One batch-recovery sample at the register widths fixed by `N`. -/
abbrev PreparedBatchSample (N : Nat) : Type :=
  BatchRecovery.PreparedSample N (registerParameters N).m
    (registerParameters N).ell

/-- Reinterpret the actual terminal outcome at the source register split. -/
def terminalBitsOfOutcome {N : Nat}
    (outcome : TerminalZMeasure.Outcome (measurementBits N)) :
    BatchRecovery.ShortLogTerminalBits (shortLogBits N) (tradeoffBits N) :=
  outcome

/-- Seal the shared prepared residue together with one actual terminal result. -/
def preparedSampleOfMeasurement {N : Nat}
    (sample : Fin (2 ^ residueSamplingBits N))
    (measurement : TerminalZMeasure.Outcome (measurementBits N)) :
    PreparedBatchSample N where
  prepared := preparedResidue sample
  terminalBits := terminalBitsOfOutcome measurement

/-- Actual Born law for one terminal result of the fixed selected member. -/
def fixedPreparedSamplePMF {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    PMF (PreparedBatchSample N) :=
  (selectedOutcomePMF (parameterValue input sample)).map
    (preparedSampleOfMeasurement sample)

/-- Sixteen fresh terminal measurements of the same internally selected
prepared residue. -/
def fixedBatchInputPMF {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    PMF (List.Vector (PreparedBatchSample N) 16) :=
  PMF.independentReplicateVector (fixedPreparedSamplePMF input sample) 16

/-- Closed output law for all 120 recovery pairs of one fixed prepared unit. -/
def fixedBatchOutputPMF {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) : PMF (Option Nat) :=
  (fixedBatchInputPMF input sample).map
    (BatchRecovery.batchValue N (registerParameters N).m
      (registerParameters N).ell)

/-- Successful fixed-generator batch outputs are checked nontrivial factors. -/
lemma fixedBatchOutputPMF_some_sound {N factor : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (member : some factor ∈ (fixedBatchOutputPMF input sample).support) :
    factor ∣ N ∧ 1 < factor ∧ factor < N := by
  rw [fixedBatchOutputPMF, PMF.mem_support_map_iff] at member
  rcases member with ⟨samples, _samplesMember, result⟩
  exact BatchRecovery.batchValue_some_sound result

/-- One complete internally sampled batch: sample the residue once, then run
the fixed-member sixteen-measurement law and closed recovery. -/
def sampledBatchOutputPMF {N : Nat} (input : Input N) : PMF (Option Nat) :=
  (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).bind
    (fixedBatchOutputPMF input)

/-- Every successful internally sampled batch output is a nontrivial factor. -/
lemma sampledBatchOutputPMF_some_sound {N factor : Nat} (input : Input N)
    (member : some factor ∈ (sampledBatchOutputPMF input).support) :
    factor ∣ N ∧ 1 < factor ∧ factor < N := by
  rw [sampledBatchOutputPMF, PMF.mem_support_bind_iff] at member
  rcases member with ⟨sample, _sampleMember, result⟩
  exact fixedBatchOutputPMF_some_sound input sample result

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical
