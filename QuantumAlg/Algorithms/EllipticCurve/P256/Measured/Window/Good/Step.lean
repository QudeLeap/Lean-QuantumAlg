/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Address
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Prefix
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Coordinates

/-!
# The original branch digit in its physical chronological window

The generic source-feed coordinate laws specialize to the unchanged original
full-q branch and the same chronological address.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

private lemma sourceFedRaw_original_address {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (position : Fin 34) (raw : Raw) :
    let index := Sampling.chronologicalIndex position
    (Tables.selectedRow index.stream index.lowerWidth index.lowerWidth_bound
      (Sampling.sourceFedRaw parameters index
        (Sampling.remainingSource index.sourceStart (sourceBranch I branch)) raw)).val =
      FullRange.chronologicalAddress I branch position := by
  dsimp only
  exact (congrArg Fin.val (Sampling.sourceFedRaw_selectedRow parameters
    (Sampling.chronologicalIndex position)
    (Sampling.remainingSource (Sampling.chronologicalIndex position).sourceStart
      (sourceBranch I branch)) raw)).trans
    ((congrArg Fin.val (parameters.remainingSource_current
      (Sampling.chronologicalIndex position) (sourceBranch I branch))).trans
      (sampling_sourcePartition_chronologicalAddress parameters I branch position))

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
