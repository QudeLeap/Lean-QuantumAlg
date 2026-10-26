/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.Coordinates
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Partition.Cast
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Partition.Replacement

/-!
# The original paired source selects and replaces the same current block

The actual sampler's source partition is retained. Its selected value and
complete current replacement agree with the symbolic contiguous segments
of that same pair. Every saved source coordinate remains present, even
though the two complement descriptions use different carriers.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open QuantumFourierTransform.Semiclassical.Window.Source

variable {ctx : RuntimeCtx .quantum}

namespace Parameters

private lemma source_positions_cast (parameters : Parameters ctx) (index : WindowIndex) :
    streamPositions (parameters.ports index) =
      castPositions index.windowIndex_sourceWidths
        (segmentPositions index.sourceStart (index.lowerWidth + 1) index.sourceAfter) := by
  apply Function.Embedding.ext
  exact parameters.sampling_source_positions index

/-- The actual source feed reads exactly the original current contiguous block. -/
lemma sampling_source_partition_selected (parameters : Parameters ctx) (index : WindowIndex)
    (label : SourceRegister.Index) :
    (parameters.sourcePartition index label).1 =
      (segmentPartition index.sourceStart (index.lowerWidth + 1) index.sourceAfter
        (sourceLabelEquiv index label)).1 := by
  change (pairedPartition 260 (streamPositions (parameters.ports index)) label).1 = _
  rw [source_positions_cast]
  exact (window_sourcePaired_cast_selected 260 _ index.windowIndex_sourceWidths
    (segmentPositions index.sourceStart (index.lowerWidth + 1) index.sourceAfter) label).trans
      (window_sourcePartition_segment_selected _ _ _ _)

/-- Replacing the current block retains exactly the same original paired source. -/
lemma sampling_source_partition_replace (parameters : Parameters ctx) (index : WindowIndex)
    (label : SourceRegister.Index) (current : (Qubits (index.lowerWidth + 1)).Index) :
    sourceLabelEquiv index ((parameters.sourcePartition index).symm
        (current, (parameters.sourcePartition index label).2)) =
      (segmentPartition index.sourceStart (index.lowerWidth + 1) index.sourceAfter).symm
        (current, (segmentPartition index.sourceStart (index.lowerWidth + 1) index.sourceAfter
          (sourceLabelEquiv index label)).2) := by
  change pairedLabelEquiv 260 _ index.windowIndex_sourceWidths
    ((pairedPartition 260 (streamPositions (parameters.ports index))).symm
      (current, (pairedPartition 260 (streamPositions (parameters.ports index)) label).2)) = _
  rw [source_positions_cast]
  exact (window_sourcePaired_cast_replace 260 _ index.windowIndex_sourceWidths
    (segmentPositions index.sourceStart (index.lowerWidth + 1) index.sourceAfter)
      label current).trans (window_sourcePartition_segment_replace _ _ _ _ current)

end Parameters

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
