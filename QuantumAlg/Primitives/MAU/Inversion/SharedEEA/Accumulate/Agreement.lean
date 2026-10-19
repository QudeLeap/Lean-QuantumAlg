/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Accumulate.Correctness
import all QuantumAlg.Primitives.MAU.Inversion.Basic

/-!
# Agreement with the original modular-add inversion data

The canonical inverse word represents the inverse of the original unit,
including modulus one. Consequently the arbitrary-target word update
is exactly `Data.addInverseIntoTarget`. For a nontrivial modulus, the
native program realizes this action on the complete initial EEA frame
and a supplied flag of either value. Actual auxiliary preparation and
the full supported-density endpoint remain separate execution obligations.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Accumulate

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open NumberTheory.SharedEEA

/-- The mathematical word represents the inverse of the original unit for every positive modulus. -/
lemma accumulateCanonical_unit (modulus : Nat) (modulusPositive : 0 < modulus)
    (input : (ZMod modulus)ˣ) :
    CanonicalInverse.word modulus modulusPositive (input : ZMod modulus).val =
      residueWord modulus modulusPositive (inverseResidue input) := by
  let : NeZero modulus := ⟨Nat.ne_of_gt modulusPositive⟩
  apply Fin.ext
  change (((input : ZMod modulus).val : ZMod modulus)⁻¹).val =
    (inverseResidue input).val
  rw [ZMod.natCast_zmod_val, ZMod.inv_coe_unit]
  rfl

/-- Word addition agrees with the original modular target update, also for modulus one. -/
lemma accumulateOutput_unit (modulus : Nat) (modulusPositive : 0 < modulus)
    (input : (ZMod modulus)ˣ) (target : ZMod modulus) :
    output modulus modulusPositive (residueWord modulus modulusPositive input).val
        (residueWord modulus modulusPositive target) =
      residueWord modulus modulusPositive (target + inverseResidue input) := by
  let : NeZero modulus := ⟨Nat.ne_of_gt modulusPositive⟩
  apply Fin.ext
  change (target.val + (CanonicalInverse.word modulus modulusPositive
    (input : ZMod modulus).val).val) % modulus = (target + inverseResidue input).val
  rw [accumulateCanonical_unit]
  exact (ZMod.val_add target (inverseResidue input)).symm

/-- Full initial EEA storage, arbitrary modular target, and the actual supplied flag label. -/
def dataFrame (modulus : Nat) (modulusPositive : 0 < modulus) (value : Data modulus) :
    Frame modulus.size × Bool :=
  ((InitialFrame.initial modulus (residueWord modulus modulusPositive value.input),
    residueWord modulus modulusPositive value.target), value.flag)

/-- The original data action is realized with complete EEA restoration and either flag value. -/
lemma accumulateProgram_data (modulus : Nat) (nontrivial : 1 < modulus)
    (value : Data modulus) :
    (UnitaryCircuit.onBinaryPrefix BinaryLabelEncoding.bool.width
      (program modulus nontrivial)).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical (BinaryLabelEncoding.prod (frameEncoding modulus.size)
            BinaryLabelEncoding.bool).width).basisEquiv.symm
            ((BinaryLabelEncoding.prod (frameEncoding modulus.size)
              BinaryLabelEncoding.bool).encode (dataFrame modulus (by omega) value)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (BinaryLabelEncoding.prod (frameEncoding modulus.size)
          BinaryLabelEncoding.bool).width).basisEquiv.symm
          ((BinaryLabelEncoding.prod (frameEncoding modulus.size)
            BinaryLabelEncoding.bool).encode
              (dataFrame modulus (by omega) value.addInverseIntoTarget))) := by
  have actual := UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
    (environment := environment) (frameEncoding modulus.size) BinaryLabelEncoding.bool
    (program modulus nontrivial)
    _ _ value.flag (accumulateProgram_unit modulus nontrivial value.input value.target)
  rw [accumulateOutput_unit] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Accumulate
