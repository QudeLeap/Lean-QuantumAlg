/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Input
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Decode
import all QuantumAlg.Util.ExceptionalOffsetAveraging

/-!
# The original paired input is the actual paid decoder's frequency bit word

The two existing pairedInput read equations determine the complete input word.
This coordinate proof adds no execution, packing instruction, normalization,
service-state assumption, or second decoder to the recovery program.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Recovery

noncomputable section

open Execution QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open ClassicalRoutines.FiniteCyclicDLP.RawRecovery

private lemma reversed_stored_bit {ctx : RuntimeCtx .quantum} {count : Nat}
    (results : BitPosition count → CWriteRef ctx (.finite 2))
    (stream : Fin 2) (store : Store ctx) (position : Fin count) :
    decide ((store.read (.storage (results (stream, position.rev)).toCStorageRef)).toFin.val = 1) =
      (Decode.storedFrequency results stream store).val.testBit position.rev.val := by
  have physical := Partner.qftPartner_frequencyBits_decode count
    (Decode.storedStream results stream store)
  change frequencyBits count (Decode.storedFrequency results stream store) =
    Decode.storedStream results stream store at physical
  rw [← Decode.windowDecode_storedStream_coordinate results stream store position.rev,
    ← physical, Partner.qftPartner_frequency_reversed_coordinate,
    BinaryBasis.bigEndianEquiv_symm_value]
  generalize (Decode.storedFrequency results stream store).val.testBit position.rev.val = value
  cases value <;> rfl

private lemma pairedInput_first_bit {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (store : Store ctx) (position : Fin 260) :
    (Native.measuredDecodeInput (store.read (pairedInput parameters))).bits
        (position.castAdd 260) =
      (Decode.storedFrequency parameters.results.cells 0 store).val.testBit position.rev.val := by
  change decide (((store.read (pairedInput parameters)).get
    (position.castAdd 260)).toFin.val = 1) = _
  rw [pairedInput_first]
  exact reversed_stored_bit parameters.results.cells 0 store position

private lemma pairedInput_second_bit {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (store : Store ctx) (position : Fin 260) :
    (Native.measuredDecodeInput (store.read (pairedInput parameters))).bits
        (position.natAdd 260) =
      (Decode.storedFrequency parameters.results.cells 1 store).val.testBit position.rev.val := by
  change decide (((store.read (pairedInput parameters)).get
    (position.natAdd 260)).toFin.val = 1) = _
  rw [pairedInput_second]
  exact reversed_stored_bit parameters.results.cells 1 store position

/-- The one existing paired input contains exactly the two original big-endian frequencies. -/
lemma pairedInput_frequency_bits {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (store : Store ctx) :
    (Native.measuredDecodeInput (store.read (pairedInput parameters))).bits =
      ExceptionalOffsetAveraging.pairedBigEndianSelected 260
        (Decode.storedFrequency parameters.results.cells 0 store,
          Decode.storedFrequency parameters.results.cells 1 store) := by
  funext index
  refine Fin.addCases (m := 260) (n := 260) (fun position => ?_)
    (fun position => ?_) index
  · rw [pairedInput_first_bit]
    simp only [ExceptionalOffsetAveraging.pairedBigEndianSelected,
      Fin.val_castAdd, dif_pos position.isLt, Fin.val_rev]
    congr 1
    omega
  · rw [pairedInput_second_bit]
    have outside : ¬260 + position.val < 260 := Nat.not_lt.mpr (Nat.le_add_right 260 _)
    simp only [ExceptionalOffsetAveraging.pairedBigEndianSelected, Fin.val_natAdd,
      dif_neg outside, Nat.add_sub_cancel_left, Fin.val_rev]
    congr 1
    omega

end

end Recovery

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
