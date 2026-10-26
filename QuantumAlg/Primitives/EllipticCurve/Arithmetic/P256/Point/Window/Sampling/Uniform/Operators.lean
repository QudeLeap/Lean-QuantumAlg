/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Uniform.Partition
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Segments.Transport

/-!
# Remaining preparation on the original paired mathematical source

All operators act on the same original pair of exponent labels. The source
partition is only a complete coordinate description. The source zero support
used below belongs to the mathematical input; physical bank zero is supplied
separately by the real active reset. No arithmetic or physical source state
is assumed here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

noncomputable section

open QuantumFourierTransform.Semiclassical.Window.Source

/-- Complete saved source segments in the original paired-source coordinate description. -/
abbrev SourceSaved (index : WindowIndex) : Register :=
  (Qubits index.sourceStart).prod (Qubits index.sourceAfter)

/-- Current and saved coordinates of the same original pair of source labels. -/
def sourceSegments (index : WindowIndex) :
    SourceRegister.Index ≃ (Qubits (index.lowerWidth + 1)).Index × (SourceSaved index).Index :=
  (sourceLabelEquiv index).trans
    (segmentPartition index.sourceStart (index.lowerWidth + 1) index.sourceAfter)

/-- Prepare only the remaining mathematical source, retaining its consumed prefix. -/
def sourceFuture (index : WindowIndex) : UnitaryOperator SourceRegister :=
  UnitaryOperator.reindex (sourceLabelEquiv index).symm
    (futurePreparation index.sourceStart ((index.lowerWidth + 1) + index.sourceAfter))

/-- The same later tensor retains the current source and every external-reference coordinate. -/
def sourceTail (index : WindowIndex) (Reference : Register) :
    UnitaryOperator ((SourceSaved index).prod Reference) :=
  UnitaryOperator.prodTensor
    (UnitaryOperator.prodTensor (1 : UnitaryOperator (Qubits index.sourceStart))
      (uniformPreparation index.sourceAfter)) (1 : UnitaryOperator Reference)

private lemma zero_split (before after : Nat) :
    (prodEquiv (m := before) (n := after)).symm 0 = (0, 0) := by
  apply Prod.ext
  · apply Fin.ext
    simp only [prodEquiv_symm_fst_val, Fin.val_zero, Nat.zero_div]
  · apply Fin.ext
    simp only [prodEquiv_symm_snd_val, Fin.val_zero, Nat.zero_mod]

/-- The original unprepared source has zero in precisely the selected current block. -/
lemma sampling_sourceSegments_zero (index : WindowIndex) :
    (sourceSegments index (0, 0)).1 = 0 := by
  change (segmentPartition index.sourceStart (index.lowerWidth + 1) index.sourceAfter
    (sourceLabelEquiv index (0, 0))).1 = 0
  rw [sampling_sourceLabel_zero]
  change ((prodEquiv (m := index.lowerWidth + 1) (n := index.sourceAfter)).symm
    ((prodEquiv (m := index.sourceStart)
      (n := (index.lowerWidth + 1) + index.sourceAfter)).symm 0).2).1 = 0
  rw [zero_split, zero_split]

variable {ctx : RuntimeCtx .quantum}

namespace Parameters

/-- The actual source feed is unchanged by the complete segment-coordinate description. -/
lemma sampling_sourceFeed_segments (parameters : Parameters ctx) (index : WindowIndex)
    (Reference : Register) :
    parameters.sourceFeed index Reference =
      selectedFeedOperator (parameters.ports index) (sourceSegments index) Reference := by
  apply window_sourceFeed_partitions_operator
  · exact parameters.sampling_source_partition_selected index
  · intro label current
    apply (sourceLabelEquiv index).injective
    exact (parameters.sampling_source_partition_replace index label current).trans
      ((sourceLabelEquiv index).apply_symm_apply _).symm

end Parameters

/-- The remaining and current/saved preparations give the same full state on the original source. -/
lemma sampling_source_future_factor (index : WindowIndex) (Reference : Register)
    {Record : Type} [Fintype Record]
    (state : ExecutionState Record (ctx.register.prod (SourceRegister.prod Reference)))
    (supported : ∀ record label, label.2.1 ≠ (0, 0) →
      (state.block record).matrix label label = 0) :
    state.applyUnitary (fun _ => sourcePreparationAction Reference (sourceFuture index)) =
      (state.applyUnitary (fun _ =>
        referencePreparation (sourceSegments index) Reference)).applyUnitary
          (fun _ => savedPreparation (sourceSegments index) Reference
            (sourceTail index Reference)) := by
  apply window_source_future_transport_state (sourceLabelEquiv index) Reference state
  intro record label absent
  apply supported record label
  intro zero
  apply absent
  rw [zero, sampling_sourceLabel_zero]
  change ((prodEquiv (m := index.sourceStart)
    (n := (index.lowerWidth + 1) + index.sourceAfter)).symm 0).2 = 0
  rw [zero_split]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
