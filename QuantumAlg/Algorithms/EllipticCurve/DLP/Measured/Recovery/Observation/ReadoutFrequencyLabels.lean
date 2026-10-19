/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.OutcomeLabels
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Output.Coordinates
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Full physical readout words and canonical Fourier frequency pairs

The two blocks are split in their actual chronological order. Recursive bit
tuples use the existing big-endian coordinates, and canonical frequencies keep
the existing bit reversal. Both changes are finite label equivalences, including
zero width; they allocate no register and execute no packing instruction.

Composing these equivalences with actual legal-path reconstruction preserves
the complete original Store, every point outcome and every physical bit. The
additive reindexing does not assert completeness or discard zero CP branches.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ReadoutFrequencyLabels

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.QuantumFourierTransform
open QuantumFourierTransform.Semiclassical
open Recovery.Stage.PointCoordinates
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity
open ActualFeedback ActualOutcomeLabels
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Chronological coordinates and recursive physical tuples describe the same full block. -/
def coordinateTupleEquiv (m : Nat) : (Fin m → Fin 2) ≃ Bits m :=
  (BinaryBasis.bigEndianEquiv m).trans (binaryEquiv m).symm

lemma coordinateTupleEquiv_symm (m : Nat) (output : Bits m) :
    (coordinateTupleEquiv m).symm output = tupleCoordinates m output := rfl

private lemma position_false {m : Nat} (current : Fin m) :
    position false current =
      (finCongr (Nat.two_mul m)).symm (Fin.castAdd m current) := by
  apply Fin.ext
  exact position_val false current

private lemma position_true {m : Nat} (current : Fin m) :
    position true current =
      (finCongr (Nat.two_mul m)).symm (Fin.natAdd m current) := by
  apply Fin.ext
  exact position_val true current

/-- Every complete physical bit word has one first-block and one second-block tuple. -/
def wordBlocksEquiv (m : Nat) : (Fin (2 * m) → Fin 2) ≃ Bits m × Bits m :=
  (Equiv.arrowCongr (finCongr (Nat.two_mul m)) (Equiv.refl (Fin 2))).trans
    ((Fin.appendEquiv m m).symm.trans
      (Equiv.prodCongr (coordinateTupleEquiv m) (coordinateTupleEquiv m)))

lemma wordBlocksEquiv_fst (m : Nat) (bits : Fin (2 * m) → Fin 2) :
    (wordBlocksEquiv m bits).1 =
      coordinateTupleEquiv m (fun current => bits (position false current)) := by
  change coordinateTupleEquiv m (fun current =>
    bits ((finCongr (Nat.two_mul m)).symm (Fin.castAdd m current))) = _
  apply congrArg (coordinateTupleEquiv m)
  funext current
  rw [position_false]

lemma wordBlocksEquiv_snd (m : Nat) (bits : Fin (2 * m) → Fin 2) :
    (wordBlocksEquiv m bits).2 =
      coordinateTupleEquiv m (fun current => bits (position true current)) := by
  change coordinateTupleEquiv m (fun current =>
    bits ((finCongr (Nat.two_mul m)).symm (Fin.natAdd m current))) = _
  apply congrArg (coordinateTupleEquiv m)
  funext current
  rw [position_true]

/-- The total block split gives exactly the two outputs of this actual measured path. -/
lemma wordBlocksEquiv_path (width m : Nat) (path : Fin (2 * m) → Branch width m) :
    wordBlocksEquiv m (fun index => ReadoutRows.outcomeBit width m (path index).2.1) =
      (blockOutput width m path false, blockOutput width m path true) := by
  apply Prod.ext
  · exact wordBlocksEquiv_fst m (fun index => ReadoutRows.outcomeBit width m (path index).2.1)
  · exact wordBlocksEquiv_snd m (fun index => ReadoutRows.outcomeBit width m (path index).2.1)

/-- A physical tuple selects the existing complete-source frequency, with its bit reversal. -/
def tupleFrequencyEquiv (m : Nat) : Bits m ≃ Fin (2 ^ m) :=
  (binaryEquiv m).trans (qftReverseBitsPerm m)

/-- All full physical readout words correspond bijectively to both canonical frequencies. -/
def readoutFrequencyEquiv (m : Nat) :
    (Fin (2 * m) → Fin 2) ≃ Fin (2 ^ m) × Fin (2 ^ m) :=
  (wordBlocksEquiv m).trans
    (Equiv.prodCongr (tupleFrequencyEquiv m) (tupleFrequencyEquiv m))

/-- The frequency equivalence is the actual pathFrequency, with the same block order. -/
lemma readoutFrequencyEquiv_path (width m : Nat)
    (path : Fin (2 * m) → Branch width m) :
    readoutFrequencyEquiv m
        (fun index => ReadoutRows.outcomeBit width m (path index).2.1) =
      pathFrequency width m path := by
  exact congrArg (fun blocks : Bits m × Bits m =>
    (tupleFrequencyEquiv m blocks.1, tupleFrequencyEquiv m blocks.2))
    (wordBlocksEquiv_path width m path)

/-- The exact full-frequency row has the literal second-times-first physical scalar order. -/
lemma readoutFrequencyEquiv_fourier (width m : Nat)
    (path : Fin (2 * m) → Branch width m) (source : Bits m × Bits m) :
    Partner.fullRows true m
        (readoutFrequencyEquiv m
          (fun index => ReadoutRows.outcomeBit width m (path index).2.1)).2 source.2 *
      Partner.fullRows true m
        (readoutFrequencyEquiv m
          (fun index => ReadoutRows.outcomeBit width m (path index).2.1)).1 source.1 =
      Partner.fourierRows true m (blockOutput width m path true) source.2 *
        Partner.fourierRows true m (blockOutput width m path false) source.1 := by
  rw [readoutFrequencyEquiv_path]
  change Partner.fullRows true m (blockFrequency width m path true) source.2 *
    Partner.fullRows true m (blockFrequency width m path false) source.1 = _
  simp only [blockFrequency_fullRow]

/-- Full actual legal paths retain independent point outcomes and both physical tuples. -/
def pointAndBlocksEquiv (width m : Nat) (original : Store (Recovery.Layout.terminal width m)) :
    LegalRun width m (2 * m) id original ≃
      (Fin (2 * m) → PointOutcome width) × (Bits m × Bits m) :=
  (pointAndReadoutEquiv width m (2 * m) id original).trans
    (Equiv.prodCongr (Equiv.refl _) (wordBlocksEquiv m))

lemma pointAndBlocksEquiv_blocks (width m : Nat)
    (original : Store (Recovery.Layout.terminal width m))
    (run : LegalRun width m (2 * m) id original) :
    (pointAndBlocksEquiv width m original run).2 =
      (blockOutput width m run.2.val false, blockOutput width m run.2.val true) :=
  wordBlocksEquiv_path width m run.2.val

/-- Full actual legal paths have one point-outcome word and one canonical frequency pair. -/
def pointAndFrequencyEquiv (width m : Nat) (original : Store (Recovery.Layout.terminal width m)) :
    LegalRun width m (2 * m) id original ≃
      (Fin (2 * m) → PointOutcome width) × (Fin (2 ^ m) × Fin (2 ^ m)) :=
  (pointAndReadoutEquiv width m (2 * m) id original).trans
    (Equiv.prodCongr (Equiv.refl _) (readoutFrequencyEquiv m))

/-- Point Store labels keep their exact final-then-division order at every actual stage. -/
lemma pointAndFrequencyEquiv_point (width m : Nat)
    (original : Store (Recovery.Layout.terminal width m))
    (run : LegalRun width m (2 * m) id original) (current : Fin (2 * m)) :
    (pointAndFrequencyEquiv width m original run).1 current =
      ((PointOutcomeFibers.storeCoordinates width m (run.2.val current).1).1,
        (run.2.val current).2.2) := rfl

lemma pointAndFrequencyEquiv_frequency (width m : Nat)
    (original : Store (Recovery.Layout.terminal width m))
    (run : LegalRun width m (2 * m) id original) :
    (pointAndFrequencyEquiv width m original run).2 = pathFrequency width m run.2.val :=
  readoutFrequencyEquiv_path width m run.2.val

/-- Legal CP label sums reindex over all point outcomes and all frequency pairs exactly once. -/
lemma legal_sum_point_frequency {Value : Type} [AddCommMonoid Value]
    (width m : Nat) (original : Store (Recovery.Layout.terminal width m))
    (term : Store (Recovery.Layout.terminal width m) → (Fin (2 * m) → Branch width m) → Value) :
    (∑ final : Store (Recovery.Layout.terminal width m), ∑ path : Fin (2 * m) → Branch width m,
      if traceValid width m (2 * m) id path original final then term final path else 0) =
      ∑ points : Fin (2 * m) → PointOutcome width,
        ∑ frequency : Fin (2 ^ m) × Fin (2 ^ m),
          term ((pointAndFrequencyEquiv width m original).symm (points, frequency)).1
            ((pointAndFrequencyEquiv width m original).symm (points, frequency)).2.val := by
  calc
    _ = ∑ run : LegalRun width m (2 * m) id original, term run.1 run.2.val := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro final _
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun _ => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]) (term final)
    _ = ∑ choices : (Fin (2 * m) → PointOutcome width) ×
          (Fin (2 ^ m) × Fin (2 ^ m)),
        term ((pointAndFrequencyEquiv width m original).symm choices).1
          ((pointAndFrequencyEquiv width m original).symm choices).2.val :=
      ((pointAndFrequencyEquiv width m original).symm.sum_comp
        (fun run => term run.1 run.2.val)).symm
    _ = _ := by rw [Fintype.sum_prod_type]

end

end ReadoutFrequencyLabels
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
