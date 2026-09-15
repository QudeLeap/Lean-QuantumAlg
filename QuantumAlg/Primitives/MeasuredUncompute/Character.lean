/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.PhaseCorrection
import all QuantumAlg.Primitives.WalshHadamard
import Mathlib.Data.Finset.Card

/-!
# The actual Pauli correction has the measured Hadamard character

For an encoded word whose bit lenses read its original little-endian value,
the actual selected Z sequence contributes exactly the Walsh-Hadamard sign.
This identifies the correction with the phase introduced by measuring the
Hadamard-transformed arithmetic word, rather than assuming a phase oracle
[LYL+26, sec_point_add/sec_point_add.tex:67-105].
-/

namespace QuantumAlg.MeasuredUncompute

noncomputable section

open EncodedBit.Word

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {width : Nat}

private theorem selected_sign_power (word : EncodedBit.Word encoding width)
    (state : Data) (indices : List (Fin width)) :
    PhaseCorrection.sign word state indices = (-1 : ℂ) ^
      (indices.filter (fun index => (word.bit index).get state)).length := by
  induction indices with
  | nil => simp [PhaseCorrection.sign]
  | cons index rest induction =>
      cases bit : (word.bit index).get state <;>
        simp [PhaseCorrection.sign, bit, induction, pow_succ, mul_comm]

/-- The executed correction sign is the same binary character as the actual Hadamard layer. -/
theorem measuredCorrection_sign_walsh (word : EncodedBit.Word encoding width)
    (state : Data) (value outcome : Fin (2 ^ width))
    (reads : ∀ index, (word.bit index).get state = value.val.testBit index.val) :
    PhaseCorrection.sign word state
        (PhaseCorrection.selected (fun index => outcome.val.testBit index.val)) =
      WalshHadamard.walshSign outcome value := by
  rw [selected_sign_power]
  have bits : (fun index => (word.bit index).get state) =
      (fun index : Fin width => value.val.testBit index.val) := funext reads
  rw [bits]
  let predicate := fun index : Fin width =>
    outcome.val.testBit index.val && value.val.testBit index.val
  have filtered :
      ((PhaseCorrection.selected (fun index => outcome.val.testBit index.val)).filter
        (fun index => value.val.testBit index.val)) =
      (List.finRange width).filter predicate := by
    simp only [PhaseCorrection.selected, List.filter_filter, predicate, Bool.and_comm]
  rw [filtered]
  have cardinality : ((List.finRange width).filter predicate).length =
      (Finset.univ.filter (fun index : Fin width => predicate index)).card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange width).filter predicate)]
    congr 1
    ext index
    simp
  rw [cardinality]
  unfold WalshHadamard.walshSign WalshHadamard.dotParity
  change (-1 : ℂ) ^ (Finset.univ.filter (fun index : Fin width => predicate index)).card =
    if decide (Odd (Finset.univ.filter (fun index : Fin width => predicate index)).card)
      then -1 else 1
  rw [neg_one_pow_eq_ite]
  by_cases even : Even (Finset.univ.filter (fun index : Fin width => predicate index)).card
  · simp [even, Nat.not_odd_iff_even.mpr even]
  · have odd := Nat.not_even_iff_odd.mp even
    simp [even, odd]

/-- The literal selected Z gates cancel exactly the measured Hadamard phase on a recomputed word. -/
theorem measuredCorrection_cancel_walsh_ket (word : EncodedBit.Word encoding width)
    (state : Data) (value outcome : Fin (2 ^ width))
    (reads : ∀ index, (word.bit index).get state = value.val.testBit index.val) :
    (PhaseCorrection.program word (fun index => outcome.val.testBit index.val)).applyVec
        (WalshHadamard.walshSign outcome value •
          (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec) =
      (NormalizedVector.ket (R := Qubits encoding.width) (encoding.encode state)).vec := by
  rw [← measuredCorrection_sign_walsh word state value outcome reads]
  exact PhaseCorrection.phaseCorrection_cancel_ket word
    (PhaseCorrection.selected (fun index => outcome.val.testBit index.val)) state

end

end QuantumAlg.MeasuredUncompute
