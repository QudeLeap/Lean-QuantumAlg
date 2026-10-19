/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Output.Coordinates

/-!
# The full final Store determines the complete Fourier frequency

The existing actual readout theorem determines every chronological output
from its real final cell. Reading those cells and applying the already defined
within-block bit reversal gives the complete native Fourier frequency. This
is a mathematical observation of the complete Store, not a physical packing
or permutation instruction. Dirty input cells and zero width are included.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.FinalFrequency

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.QuantumFourierTransform
open QuantumFourierTransform.Semiclassical
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity

/-- Read the actual chronological cells of one block in complete-source frequency coordinates. -/
def block (width m : Nat) (final : Store (Recovery.Layout.terminal width m)) (second : Bool) :
    Fin (2 ^ m) :=
  qftReverseBits m (BinaryBasis.bigEndianEquiv m (fun current =>
    (final.read (.storage (Recovery.Layout.resultCell width m
      (ActualFeedback.position second current)).toCStorageRef)).toFin))

/-- Observe both existing blocks in their original first-then-second order. -/
def pair (width m : Nat) (final : Store (Recovery.Layout.terminal width m)) :
    Fin (2 ^ m) × Fin (2 ^ m) :=
  (block width m final false, block width m final true)

/-- On every actual legal full path, each frequency is fixed by the complete final Store. -/
lemma blockFrequency_eq_final (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Recovery.Layout.terminal width m))
    (valid : traceValid width m (2 * m) id path original final) (second : Bool) :
    ActualFeedback.blockFrequency width m path second = block width m final second := by
  unfold ActualFeedback.blockFrequency ActualFeedback.blockOutput block
  rw [Equiv.apply_symm_apply]
  apply congrArg (qftReverseBits m)
  apply congrArg (BinaryBasis.bigEndianEquiv m)
  funext current
  have written := FeedbackReads.full_trace_final_read width m path original final valid
    (ActualFeedback.position second current)
  exact (congrArg (fun value => value.toFin) written).symm

/-- Every legal path in the same complete final Store fiber has exactly the same frequency pair. -/
lemma pathFrequency_eq_final (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Recovery.Layout.terminal width m))
    (valid : traceValid width m (2 * m) id path original final) :
    ActualFeedback.pathFrequency width m path = pair width m final := by
  apply Prod.ext
  · exact blockFrequency_eq_final width m path original final valid false
  · exact blockFrequency_eq_final width m path original final valid true

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.FinalFrequency
