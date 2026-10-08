/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Division.SharedEEA.Correctness
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Agreement
import all QuantumAlg.Primitives.MAU.Division.Basic

/-!
# Agreement with the original modular-add division data

The unchanged original numerator multiplies the inverse of the original
unit denominator. The native target update therefore has precisely the
meaning of `Data.addQuotientIntoTarget`, for any modular numerator and
target. The mathematical agreement includes modulus one. The native
nontrivial branch restores its entire EEA frame and either flag value;
actual preparation and complete mixed-state execution are separate layers.
-/

namespace QuantumAlg.MAU.Division.SharedEEA

noncomputable section

open NumberTheory.SharedEEA Inversion.SharedEEA

/-- Word quotient addition is the original residue action for every positive modulus. -/
theorem divisionOutput_unit (modulus : Nat) (modulusPositive : 0 < modulus)
    (denominator : (ZMod modulus)ˣ) (numerator target : ZMod modulus) :
    output modulus modulusPositive (Accumulate.residueWord modulus modulusPositive denominator).val
        (Accumulate.residueWord modulus modulusPositive numerator)
        (Accumulate.residueWord modulus modulusPositive target) =
      Accumulate.residueWord modulus modulusPositive
        (target + quotientResidue denominator numerator) := by
  let : NeZero modulus := ⟨Nat.ne_of_gt modulusPositive⟩
  apply Fin.ext
  change (target.val + (CanonicalInverse.word modulus modulusPositive
    (denominator : ZMod modulus).val).val * numerator.val) % modulus =
      (target + numerator * Inversion.inverseResidue denominator).val
  rw [Accumulate.accumulateCanonical_unit, ZMod.val_add, ZMod.val_mul, Nat.add_mod_mod]
  change (target.val + (Inversion.inverseResidue denominator).val * numerator.val) % modulus = _
  rw [Nat.mul_comm]

/-- The complete initial EEA frame carries all original division fields, including its live flag. -/
def dataFrame (modulus : Nat) (modulusPositive : 0 < modulus) (value : Data modulus) :
    Frame modulus.size × Bool :=
  ((InitialFrame.initial modulus
      (Accumulate.residueWord modulus modulusPositive value.denominator),
    Accumulate.residueWord modulus modulusPositive value.numerator,
    Accumulate.residueWord modulus modulusPositive value.target), value.flag)

/-- Native quotient accumulation realizes the original data map and restores every EEA field. -/
theorem divisionProgram_data (modulus : Nat) (nontrivial : 1 < modulus)
    (value : Data modulus) :
    (UnitaryCircuit.onBinaryPrefix BinaryLabelEncoding.bool.width
      (program modulus nontrivial)).applyNormalized
        (NormalizedVector.ket
          ((QubitLayout.canonical
            (BinaryLabelEncoding.prod (frameEncoding modulus.size)
              BinaryLabelEncoding.bool).width).basisEquiv.symm
            ((BinaryLabelEncoding.prod (frameEncoding modulus.size)
              BinaryLabelEncoding.bool).encode (dataFrame modulus (by omega) value)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
          (BinaryLabelEncoding.prod (frameEncoding modulus.size)
            BinaryLabelEncoding.bool).width).basisEquiv.symm
          ((BinaryLabelEncoding.prod (frameEncoding modulus.size)
            BinaryLabelEncoding.bool).encode
              (dataFrame modulus (by omega) value.addQuotientIntoTarget))) := by
  have actual := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (frameEncoding modulus.size) BinaryLabelEncoding.bool (program modulus nontrivial)
    _ _ value.flag
    (divisionProgram_unit modulus nontrivial value.denominator value.numerator value.target)
  rw [divisionOutput_unit] at actual
  exact actual

end

end QuantumAlg.MAU.Division.SharedEEA
