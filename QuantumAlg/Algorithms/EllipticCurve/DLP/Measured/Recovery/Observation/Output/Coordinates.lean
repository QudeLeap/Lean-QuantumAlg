/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.BlockRows
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency
import all QuantumAlg.Util.ExceptionalOffsetAveraging
import Lean.Elab.Tactic.Omega

/-!
# Actual streaming terminal cells and complete-source Fourier coordinates

Each terminal cell is the actual outcome of its own stage, including arbitrary dirty
initial cell values. The complete native Fourier frequency is the bit reversal of each
chronological block. The coordinate laws below preserve that reversal explicitly; they
do not execute a free packing instruction or identify two different result Stores. All
finite laws include width zero without a positivity premise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord.PathDensity
namespace FeedbackReads

noncomputable section

open QuantumAlg QuantumAlg.Execution
open Recovery.Stage.PointCoordinates.ReadoutRows

/-- An actual suffix preserves a real result cell that it never writes. -/
private lemma traceValid_final_unwritten (width m : Nat) (count : Nat)
    (indices : Fin count → Fin (2 * m)) (path : Fin count → Branch width m)
    (original final : Store (Recovery.Layout.terminal width m))
    (valid : traceValid width m count indices path original final)
    (observed : Fin (2 * m)) (avoids : ∀ index, indices index ≠ observed) :
    final.read (.storage (Recovery.Layout.resultCell width m observed).toCStorageRef) =
      original.read (.storage (Recovery.Layout.resultCell width m observed).toCStorageRef) := by
  induction count generalizing original final with
  | zero => cases valid; rfl
  | succ count ih =>
      obtain ⟨retained, tailValid⟩ := valid
      exact (ih (Fin.tail indices) (Fin.tail path)
        (written width m (indices 0) (path 0)) final tailValid
        (fun index => avoids index.succ)).trans
          ((written_resultCell_other width m (indices 0) observed (avoids 0) (path 0)).trans
            (retains_resultCell width m (path 0).1 original retained observed))

/-- Every distinct actual stage leaves its measured value in its complete final Store. -/
lemma traceValid_final_read (width m : Nat) (count : Nat)
    (indices : Fin count → Fin (2 * m)) (path : Fin count → Branch width m)
    (original final : Store (Recovery.Layout.terminal width m))
    (valid : traceValid width m count indices path original final)
    (distinct : Function.Injective indices) (current : Fin count) :
    final.read (.storage (Recovery.Layout.resultCell width m (indices current)).toCStorageRef) =
      .finite (outcomeBit width m (path current).2.1) := by
  induction count generalizing original final with
  | zero => exact Fin.elim0 current
  | succ count ih =>
      obtain ⟨_, tailValid⟩ := valid
      refine Fin.cases ?_ (fun current => ?_) current
      · have avoids : ∀ index : Fin count, (Fin.tail indices) index ≠ indices 0 := by
          intro index same
          have impossible : index.succ = (0 : Fin (count + 1)) := distinct same
          exact Nat.succ_ne_zero index.val (congrArg Fin.val impossible)
        exact (traceValid_final_unwritten width m count (Fin.tail indices) (Fin.tail path)
          (written width m (indices 0) (path 0)) final tailValid (indices 0) avoids).trans
            (written_resultCell_same width m (indices 0) (path 0))
      · have tailDistinct : Function.Injective (Fin.tail indices) := by
          intro left right same
          exact Fin.succ_injective _ (distinct same)
        exact ih (Fin.tail indices) (Fin.tail path)
          (written width m (indices 0) (path 0)) final tailValid tailDistinct current

/-- The complete original-order streaming execution records every actual physical output. -/
lemma full_trace_final_read (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (original final : Store (Recovery.Layout.terminal width m))
    (valid : traceValid width m (2 * m) id path original final) (index : Fin (2 * m)) :
    final.read (.storage (Recovery.Layout.resultCell width m index).toCStorageRef) =
      .finite (outcomeBit width m (path index).2.1) :=
  traceValid_final_read width m (2 * m) id path original final valid
    Function.injective_id index

end

end FeedbackReads

namespace ActualFeedback

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.QuantumFourierTransform
open QuantumFourierTransform.Semiclassical
open Recovery.Stage.PointCoordinates

/-- The complete-source frequency selected by one actual chronological output block. -/
def blockFrequency (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (second : Bool) : Fin (2 ^ m) :=
  qftReverseBits m (binaryEquiv m (blockOutput width m path second))

/-- Both complete-source frequencies retain the original first-then-second block order. -/
def pathFrequency (width m : Nat) (path : Fin (2 * m) → Branch width m) :
    Fin (2 ^ m) × Fin (2 ^ m) :=
  (blockFrequency width m path false, blockFrequency width m path true)

/-- Decoding the selected complete frequency gives the exact actual physical output tuple. -/
lemma blockFrequency_decode (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (second : Bool) :
    frequencyBits m (blockFrequency width m path second) =
      blockOutput width m path second :=
  Partner.qftPartner_frequencyBits_decode m (blockOutput width m path second)

/-- The literal complete native inverse-QFT row equals the actual chronological row. -/
lemma blockFrequency_fullRow (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (second : Bool) (input : Bits m) :
    Partner.fullRows true m (blockFrequency width m path second) input =
      Partner.fourierRows true m (blockOutput width m path second) input := by
  rw [Partner.qftPartner_fullRows_physical, blockFrequency_decode]

private lemma paired_selected_position {m : Nat}
    (frequency : Fin (2 ^ m) × Fin (2 ^ m)) (second : Bool) (current : Fin m) :
    ExceptionalOffsetAveraging.pairedBigEndianSelected m frequency (position second current) =
      finTwoEquiv ((BinaryBasis.bigEndianEquiv m).symm
        (if second then frequency.2 else frequency.1) current) := by
  have reversed : current.rev.val = m - 1 - current.val := by
    rw [Fin.val_rev]
    omega
  cases second with
  | false =>
      simp only [ExceptionalOffsetAveraging.pairedBigEndianSelected, position_val,
        Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, current.isLt,
        BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply, reversed]
  | true =>
      have beyond : ¬ m + current.val < m := by omega
      simp only [ExceptionalOffsetAveraging.pairedBigEndianSelected, position_val,
        ↓reduceIte, ↓reduceDIte, beyond, Nat.add_sub_cancel_left,
        BinaryBasis.bigEndianEquiv_symm_value, Equiv.apply_symm_apply, reversed]

/-- Canonical frequency bits read the reversed actual positions inside each block. -/
lemma pathFrequency_selected_position (width m : Nat)
    (path : Fin (2 * m) → Branch width m) (second : Bool) (current : Fin m) :
    ExceptionalOffsetAveraging.pairedBigEndianSelected m (pathFrequency width m path)
        (position second current) =
      finTwoEquiv (ReadoutRows.outcomeBit width m
        (path (position second current.rev)).2.1) := by
  rw [paired_selected_position]
  have selected : (if second then (pathFrequency width m path).2
      else (pathFrequency width m path).1) = blockFrequency width m path second := by
    cases second <;> rfl
  rw [selected, ← Partner.qftPartner_frequency_reversed_coordinate,
    blockFrequency_decode, blockOutput_coordinate]

/-- Each reversed actual terminal cell contains the corresponding canonical frequency bit. -/
lemma pathFrequency_final_store_coordinate (width m : Nat)
    (path : Fin (2 * m) → Branch width m)
    (original final : Store (Recovery.Layout.terminal width m))
    (valid : traceValid width m (2 * m) id path original final)
    (second : Bool) (current : Fin m) :
    final.read (.storage
        (Recovery.Layout.resultCell width m (position second current.rev)).toCStorageRef) =
      .finite (finTwoEquiv.symm
        (ExceptionalOffsetAveraging.pairedBigEndianSelected m (pathFrequency width m path)
          (position second current))) := by
  rw [FeedbackReads.full_trace_final_read width m path original final valid,
    pathFrequency_selected_position, Equiv.symm_apply_apply]

end

end ActualFeedback
end PointCoordinates.StageWord.PathWord.PathDensity
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
