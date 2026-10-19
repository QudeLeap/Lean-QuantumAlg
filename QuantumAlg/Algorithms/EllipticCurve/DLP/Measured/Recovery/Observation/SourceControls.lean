/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.PointWords
import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.Bank.AffineTrajectory
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.BlockRows
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.ExceptionalOffsetAveraging
import all QuantumAlg.Util.FinPow.BinaryBasis
import Mathlib.Data.List.FinRange
import Lean.Elab.Tactic.Omega

/-!
# Original source controls and the complete actual stage schedule

The original pair of binary values uses the same two recursive source tuples.
Its big-endian Boolean selector encodes to precisely the actual physical tuple
coordinate at every stage. Lifting both actual block lists to that common
source and concatenating them gives the original full affine schedule.

The original exceptional-offset good predicate therefore supplies the existing
local bank-word domain without an extra certificate. These are mathematical
coordinate identities; no source is normalized, no outcome is discarded, and
no runtime circuit or scalar compiler is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.SourceControls

noncomputable section

private lemma bool_encode_finTwo (value : Bool) :
    BinaryLabelEncoding.bool.encode value = finTwoEquiv.symm value := by
  cases value <;> rfl

open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (Bits binaryEquiv tupleCoordinates)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.ActualFeedback
  (position position_val)

/-- The same original binary pair, before any Fourier frequency reversal. -/
def sourceValues (m : Nat) (source : Bits m × Bits m) : Fin (2 ^ m) × Fin (2 ^ m) :=
  (binaryEquiv m source.1, binaryEquiv m source.2)

/-- The unchanged original selector, evaluated at the actual coherent source. -/
def controls (m : Nat) (source : Bits m × Bits m) (index : Fin (2 * m)) : Bool :=
  ExceptionalOffsetAveraging.pairedBigEndianSelected m (sourceValues m source) index

/-- Each original block retains its own component of the complete source pair. -/
def blockSource {m : Nat} (second : Bool) (source : Bits m × Bits m) : Bits m :=
  if second then source.2 else source.1

/-- Original big-endian selection is exactly the physical tuple coordinate. -/
lemma controls_position (m : Nat) (source : Bits m × Bits m)
    (second : Bool) (current : Fin m) :
    BinaryLabelEncoding.bool.encode (controls m source (position second current)) =
      tupleCoordinates m (blockSource second source) current := by
  have reverse : m - 1 - current.val = current.rev.val := by
    rw [Fin.val_rev, Nat.sub_sub, Nat.add_comm]
  cases second with
  | false =>
      change BinaryLabelEncoding.bool.encode
          (ExceptionalOffsetAveraging.pairedBigEndianSelected m (sourceValues m source)
            (position false current)) = tupleCoordinates m source.1 current
      rw [ExceptionalOffsetAveraging.pairedBigEndianSelected, position_val]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [dif_pos current.isLt, bool_encode_finTwo, reverse]
      exact (BinaryBasis.bigEndianEquiv_symm_value m (binaryEquiv m source.1) current).symm
  | true =>
      change BinaryLabelEncoding.bool.encode
          (ExceptionalOffsetAveraging.pairedBigEndianSelected m (sourceValues m source)
            (position true current)) = tupleCoordinates m source.2 current
      rw [ExceptionalOffsetAveraging.pairedBigEndianSelected, position_val]
      simp only [↓reduceIte]
      have notFirst : ¬ m + current.val < m := by omega
      rw [dif_neg notFirst, Nat.add_sub_cancel_left, bool_encode_finTwo, reverse]
      exact (BinaryBasis.bigEndianEquiv_symm_value m (binaryEquiv m source.2) current).symm

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}

/-- The actual block list, with its control function lifted to the same full source. -/
def blockStages (points : Fin (2 * m) → AffinePoint E) (second : Bool) :
    List (ControlledPointWords.Stage E (Bits m × Bits m)) :=
  (ActualPointWords.blockStages E points second).map (fun stage =>
    (stage.1, fun source => stage.2 (blockSource second source)))

omit [Fact p.Prime] in
/-- Every lifted actual stage has its original affine point and original Boolean selector. -/
lemma blockStages_eq (points : Fin (2 * m) → AffinePoint E) (second : Bool) :
    blockStages E points second =
      List.ofFn (fun current : Fin m =>
        (points (position second current), fun source : Bits m × Bits m =>
          BinaryLabelEncoding.bool.encode (controls m source (position second current)))) := by
  unfold blockStages ActualPointWords.blockStages
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext current
  apply Prod.ext
  · rfl
  · funext source
    exact (controls_position m source second current).symm

private lemma ofFn_split_positions {Value : Type} (m : Nat)
    (entry : Fin (2 * m) → Value) :
    List.ofFn entry =
      List.ofFn (fun current : Fin m => entry (position false current)) ++
        List.ofFn (fun current : Fin m => entry (position true current)) := by
  rw [List.ofFn_congr (Nat.two_mul m), List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext current
    apply congrArg entry
    apply Fin.ext
    exact (position_val false current).symm
  · apply congrArg List.ofFn
    funext current
    apply congrArg entry
    apply Fin.ext
    exact (position_val true current).symm

omit [Fact p.Prime] in
/-- First then second is the complete original affine schedule in chronological order. -/
lemma blockStages_append_affineStages (points : Fin (2 * m) → AffinePoint E) :
    blockStages E points false ++ blockStages E points true =
      PointBankAffineTrajectory.affineStages E points (controls m) (List.finRange (2 * m)) := by
  rw [blockStages_eq, blockStages_eq, PointBankAffineTrajectory.affineStages,
    ← List.ofFn_eq_map]
  exact (ofFn_split_positions m (fun index =>
    (points index, fun source : Bits m × Bits m =>
      BinaryLabelEncoding.bool.encode (controls m source index)))).symm

/-- The same original good source supplies the domain of the concatenated actual bank word. -/
lemma wordAllowed_original_good (points : Fin (2 * m) → AffinePoint E)
    (source : Bits m × Bits m) (initial : AffinePoint E)
    (good : ExceptionalOffsetAveraging.Admissible (2 * m)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected m)
      (fun index => (points index).toGroupPoint) initial.toGroupPoint (sourceValues m source)) :
    PointWordGoodColumns.wordAllowed E
      (blockStages E points false ++ blockStages E points true)
      source (PointBankAffineTrajectory.fieldWords initial) := by
  rw [blockStages_append_affineStages]
  exact PointBankAffineTrajectory.wordAllowed_finRange_of_group E points (controls m)
    source initial good

/-- The same actual stage list ends at the original good affine trajectory. -/
lemma wordResult_original_good (points : Fin (2 * m) → AffinePoint E)
    (source : Bits m × Bits m) (initial : AffinePoint E)
    (good : ExceptionalOffsetAveraging.Admissible (2 * m)
      (ExceptionalOffsetAveraging.pairedBigEndianSelected m)
      (fun index => (points index).toGroupPoint) initial.toGroupPoint (sourceValues m source)) :
    PointWordGoodColumns.wordResult E
        (blockStages E points false ++ blockStages E points true)
        source (PointBankAffineTrajectory.fieldWords initial) =
      PointBankAffineTrajectory.fieldWords
        (ScalarMultiplication.AffineTrajectory.path E points (controls m source)
          (List.finRange (2 * m)) initial) := by
  rw [blockStages_append_affineStages]
  exact PointBankAffineTrajectory.wordResult_finRange_of_group E points (controls m)
    source initial good

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.SourceControls
