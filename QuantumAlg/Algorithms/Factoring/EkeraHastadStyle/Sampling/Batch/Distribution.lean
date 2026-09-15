/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Batch.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Sampling.Distribution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.PackedSample
import all QuantumAlg.Util.PMF
import Mathlib.Probability.Distributions.Uniform

/-!
# Original same-source distribution of the complete native batch result

One uniform residue source determines the complete prepared parameter. The
existing short-DLP Born distribution of that parameter is then repeated
sixteen times. This mathematical law retains the original source bits,
early-factor data and chronological outcomes. The separate execution proof
must derive this law from actual sampling, storage, measurement and reuse.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch

noncomputable section

/-- The complete source value keeps its original sample and all chronological measured outcomes. -/
def sourceValue {N : Nat} (input : Input N) (source : Fin (2 ^ residueSamplingBits N))
    (samples : List.Vector (Fin (measurementBits N) → Bool) 16) : (resultShape N).Value :=
  .product (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits source))
    (.product (parameterValue input source)
      (.fixedVector (fun index => .bits (samples.get index))))

/-- One uniform source followed by the existing conditional vector distribution. -/
def sourceDistribution {N : Nat} (input : Input N) : PMF (resultShape N).Value :=
  (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).bind fun source =>
    (PMF.independentReplicateVector (selectedOutcomePMF (parameterValue input source)) 16).map
      (sourceValue input source)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeBatch
