/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Observation
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Partition.Stream
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Partition.Segments
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Partition.Cast

/-!
# The original two-stream source and the actual window positions

The first mathematical exponent precedes the second. The actual ports
already select contiguous original chronological positions; their numeric
offsets agree exactly with the before/current/after partition. The labels
below belong solely to the mathematical observation source. Physical wires,
retained Fourier cells and the original sampling instructions are unchanged.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open QuantumFourierTransform.Semiclassical.Window.Source

namespace WindowIndex

/-- Original paired-source offset, with the complete generator exponent first. -/
def sourceStart (index : WindowIndex) : Nat :=
  if index.stream.val = 0 then index.start else 260 + index.start

/-- Original paired-source positions after this same current block. -/
def sourceAfter (index : WindowIndex) : Nat :=
  520 - (index.sourceStart + (index.lowerWidth + 1))

lemma windowIndex_sourceWithin (index : WindowIndex) :
    index.sourceStart + (index.lowerWidth + 1) ≤ 520 := by
  have within := index.within
  by_cases first : index.stream.val = 0
  · simp only [sourceStart, if_pos first]
    omega
  · simp only [sourceStart, if_neg first]
    omega

/-- These three symbolic segments contain exactly the same two full260-bit sources. -/
lemma windowIndex_sourceWidths (index : WindowIndex) :
    index.sourceStart + ((index.lowerWidth + 1) + index.sourceAfter) = 520 := by
  have within := index.windowIndex_sourceWithin
  unfold sourceAfter
  omega

end WindowIndex

variable {ctx : RuntimeCtx .quantum}

namespace Parameters

/-- The same original ports select precisely the current contiguous mathematical source block. -/
lemma sampling_source_positions (parameters : Parameters ctx) (index : WindowIndex)
    (bit : Fin (index.lowerWidth + 1)) :
    streamPositions (parameters.ports index) bit =
      Fin.cast index.windowIndex_sourceWidths
        (segmentPositions index.sourceStart (index.lowerWidth + 1) index.sourceAfter bit) := by
  apply Fin.ext
  rw [window_source_streamPositions_val]
  rfl

end Parameters

/-- The same paired source label in the symbolic before/current/after width. -/
def sourceLabelEquiv (index : WindowIndex) :
    SourceRegister.Index ≃
      (Qubits (index.sourceStart + ((index.lowerWidth + 1) + index.sourceAfter))).Index :=
  pairedLabelEquiv 260 _ index.windowIndex_sourceWidths

/-- The mathematical source's unprepared original pair retains its exact zero label. -/
lemma sampling_sourceLabel_zero (index : WindowIndex) :
    sourceLabelEquiv index (0, 0) = 0 := by
  exact window_sourcePairedLabel_zero 260 _ index.windowIndex_sourceWidths

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
