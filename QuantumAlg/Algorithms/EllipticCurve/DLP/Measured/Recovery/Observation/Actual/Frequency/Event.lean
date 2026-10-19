/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.SourceControls
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.ReadoutFrequencyLabels
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Terminal.StoreCoordinates
import all QuantumAlg.Core.Execution.QubitReadouts

/-!
# The actual complete terminal-cell event is the same canonical frequency event

The literal original readout input reads the actual result cells, reversing
positions only inside each block. On every complete legal path those values
are precisely the paired big-endian bits of its canonical frequency. Any
predicate on the actual bit vector therefore selects the same full legal
labels as its frequency predicate. Point outcomes, dirty initial Stores, and
zero CP labels are retained; no comparison with an old execution is used.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ActualFrequencyEvent

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.QuantumFourierTransform
open QuantumFourierTransform.Semiclassical
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.ActualFeedback

/-- The unchanged structural observation reads the existing reversed result-cell positions. -/
def resultBits (width m : Nat) (stored : Store (Recovery.Layout.terminal width m)) :
    Fin (2 * m) → Bool :=
  fun index => decide ((stored.read (.storage (Recovery.Layout.resultCell width m
    (TerminalStoreCoordinates.blockReverse m index)).toCStorageRef)).toFin.val = 1)

/-- This is exactly the actual fixed-vector classical read, with no executed packing step. -/
lemma resultBits_readoutInput (width m : Nat) (stored : Store (Recovery.Layout.terminal width
  m)) :
    resultBits width m stored = QubitReadouts.mask
      (stored.read (QubitReadouts.input (fun index => Recovery.Layout.resultCell width m
        (TerminalStoreCoordinates.blockReverse m index)))) := rfl

private lemma blockReverse_position {m : Nat} (second : Bool) (current : Fin m) :
    TerminalStoreCoordinates.blockReverse m (position second current) =
      position second current.rev := by
  cases second with
  | false =>
      simp only [ReadoutFrequencyLabels.position_false]
      exact TerminalStoreCoordinates.blockReverse_left m current
  | true =>
      simp only [ReadoutFrequencyLabels.position_true]
      exact TerminalStoreCoordinates.blockReverse_right m current

/-- Every actual final observation bit is the corresponding original canonical frequency bit. -/
lemma resultBits_path (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Recovery.Layout.terminal width m))
    (valid : traceValid width m (2 * m) id path original final) :
    resultBits width m final =
      ExceptionalOffsetAveraging.pairedBigEndianSelected m (pathFrequency width m path) := by
  have coordinate (second : Bool) (current : Fin m) :
      resultBits width m final (position second current) =
        ExceptionalOffsetAveraging.pairedBigEndianSelected m (pathFrequency width m path)
          (position second current) := by
    unfold resultBits
    rw [blockReverse_position,
      pathFrequency_final_store_coordinate width m path original final valid second current]
    cases value : ExceptionalOffsetAveraging.pairedBigEndianSelected m
      (pathFrequency width m path) (position second current) <;> rfl
  apply List.ofFn_injective
  rw [SourceControls.ofFn_split_positions, SourceControls.ofFn_split_positions]
  congr 1
  · apply congrArg List.ofFn
    funext current
    exact coordinate false current
  · apply congrArg List.ofFn
    funext current
    exact coordinate true current

/-- The complete legal-label equivalence keeps the same actual final Store event. -/
lemma resultBits_legalRun (width m : Nat)
    (original : Store (Recovery.Layout.terminal width m))
    (run : ActualOutcomeLabels.LegalRun width m (2 * m) id original) :
    resultBits width m run.1 = ExceptionalOffsetAveraging.pairedBigEndianSelected m
      (ReadoutFrequencyLabels.pointAndFrequencyEquiv width m original run).2 := by
  rw [ReadoutFrequencyLabels.pointAndFrequencyEquiv_frequency]
  exact resultBits_path width m run.2.val original run.1 run.2.property

/-- Every predicate on the literal original readout vector selects precisely the same frequency. -/
lemma event_legalRun (width m : Nat)
    (original : Store (Recovery.Layout.terminal width m))
    (event : (Fin (2 * m) → Bool) → Prop)
    (run : ActualOutcomeLabels.LegalRun width m (2 * m) id original) :
    event (resultBits width m run.1) ↔
      event (ExceptionalOffsetAveraging.pairedBigEndianSelected m
        (ReadoutFrequencyLabels.pointAndFrequencyEquiv width m original run).2) := by
  rw [resultBits_legalRun]

/-- Reindexing counts every point-outcome word at each frequency with the same Store event. -/
lemma event_frequencyFiber (width m : Nat)
    (original : Store (Recovery.Layout.terminal width m))
    (event : (Fin (2 * m) → Bool) → Prop)
    (outcomes : Fin (2 * m) → ActualOutcomeLabels.PointOutcome width)
    (frequency : Fin (2 ^ m) × Fin (2 ^ m)) :
    event (resultBits width m
      ((ReadoutFrequencyLabels.pointAndFrequencyEquiv width m original).symm
        (outcomes, frequency)).1) ↔
      event (ExceptionalOffsetAveraging.pairedBigEndianSelected m frequency) := by
  simpa only [Equiv.apply_symm_apply] using event_legalRun width m original event
    ((ReadoutFrequencyLabels.pointAndFrequencyEquiv width m original).symm (outcomes, frequency))

end

end ActualFrequencyEvent
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
