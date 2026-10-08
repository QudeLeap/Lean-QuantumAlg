/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Outcome
import all QuantumAlg.Algorithms.OrderFinding.Native.Born.Distribution
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Util.PMF

/-!
# Native source sample and Born distributions for canonical Shor factoring

The source model chooses the original fixed-width uniform sample, derives its
RSA residue parameter and observes the selected native order-finding word on
the zero input. The sampled base selects the granted XOR operator but the
terminal phase law is obtained from the actual native circuit. Runtime Shor
execution must prove that its stored results have this joint law before using
the source success or independent-repetition bounds.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical

noncomputable section

/-- The declared source operator selected by the sampled public residue. -/
theorem sourceAccess {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    OrderFinding.ModExpOracleAccess N (parameterValue input sample).first.toNat
      (phaseBits N) (modulusBits N) where
  modulus_pos := input.modulus_pos
  register_fits := input.register_fits

/-- The native zero-input state after the member selected by this source sample. -/
def sourceSampleState {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    QubitLayout.State (OrderFinding.Native.sourceLayout (phaseBits N) (modulusBits N)) :=
  OrderFinding.Native.evolvedState (sourceAccess input sample)

/-- Fixed-sample Born law derived from the original selected member and phase positions. -/
def sourceSampleOutcomePMF {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    PMF (TerminalZMeasure.Outcome (phaseBits N)) :=
  OrderFinding.Native.sourceOutcomePMF (sourceAccess input sample)

/-- The source joint law retains the same sample that selects its conditional Born distribution. -/
def sourceOutcomePMF {N : Nat} (input : Input N) : PMF (SourceOutcome N) :=
  (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).bind fun sample =>
    (sourceSampleOutcomePMF input sample).map fun measurement =>
      ⟨sample, measurement⟩

end

end QuantumAlg.Factoring.ShorStyle.Canonical
