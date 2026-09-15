/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Access
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Util.PMF

/-!
# Source sample and Born distributions for canonical Shor factoring

The source model chooses the original fixed-width uniform sample, derives its
RSA residue parameter and observes the same selected order-finding operator on
the zero input. These are mathematical probability laws, with no execution,
storage, resource or borrowed-state certificate attached. A native execution
must prove that its actual stored results have this joint law before using the
source success or independent-repetition bounds.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical

noncomputable section

/-- One source sample together with the Born result for its selected circuit member. -/
structure SourceOutcome (N : Nat) where
  /-- The original little-endian finite random sample. -/
  sample : Fin (2 ^ residueSamplingBits N)
  /-- The selected member's big-endian phase-register measurement. -/
  measurement : OrderFinding.Outcome (phaseBits N)

/-- The original zero-input state after the member selected by this source sample. -/
def sourceSampleState {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    QubitLayout.State (OrderFinding.layout (phaseBits N) (modulusBits N)) where
  state := PureState.ofNormalized
    ((memberCircuit input (parameterValue input sample)).applyNormalized
      (OrderFinding.inputState (phaseBits N) (modulusBits N)).normalized)
    (OrderFinding.layout (phaseBits N) (modulusBits N)).systemIdx
  system_idx_eq := rfl

/-- Fixed-sample Born law derived from the original selected member and phase positions. -/
def sourceSampleOutcomePMF {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) : PMF (OrderFinding.Outcome (phaseBits N)) :=
  (OrderFinding.measurement (phaseBits N) (modulusBits N)).outcomePMF
    (sourceSampleState input sample)

/-- The source joint law retains the same sample that selects its conditional Born distribution. -/
def sourceOutcomePMF {N : Nat} (input : Input N) : PMF (SourceOutcome N) :=
  (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).bind fun sample =>
    (sourceSampleOutcomePMF input sample).map fun measurement =>
      ⟨sample, measurement⟩

end

end QuantumAlg.Factoring.ShorStyle.Canonical
