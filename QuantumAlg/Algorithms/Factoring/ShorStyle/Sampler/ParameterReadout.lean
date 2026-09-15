/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters

/-!
# Mathematical parameter readout for RSA residue preparation

These statements describe the unchanged deterministic RSA preparation on
rejected, coprime and noncoprime choices. Their component extensionality law
identifies the complete finite parameter value. They depend only on the
mathematical preparation and its intrinsic value encoding.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler

/-- The terminal pack is extensional in its three visible components.  This
small bridge keeps the body proof focused on the actual scan and GCD values,
rather than repeatedly unpacking the retained parameter representation. -/
theorem sampler_parameterValue_eq_of_components {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (unitWord : CShape.Value (.unsignedWord (modulusBits N)))
    (tag : CShape.Value .bit)
    (payload : CShape.Value (.unsignedWord (modulusBits N)))
    (unitValue : unitWord.toNat = (parameterValue input sample).first.toNat)
    (tagValue : tag.toBool = (parameterValue input sample).second.first.toBool)
    (payloadValue : payload.toNat = (parameterValue input sample).second.second.toNat) :
    CShape.Value.product unitWord (CShape.Value.product tag payload) =
      parameterValue input sample := by
  cases unitWord with
  | unsignedWord unitWord =>
      cases tag with
      | bit tag =>
          cases payload with
          | unsignedWord payload =>
              generalize _parameterValueEq : parameterValue input sample = expectedParameter
                at unitValue tagValue payloadValue ⊢
              cases expectedParameter with
              | product expectedUnit expectedTail =>
                  cases expectedUnit with
                  | unsignedWord expectedUnit =>
                      cases expectedTail with
                      | product expectedTag expectedPayload =>
                          cases expectedTag with
                          | bit expectedTag =>
                              cases expectedPayload with
                              | unsignedWord expectedPayload =>
                                  change unitWord.val = expectedUnit.val at unitValue
                                  change tag = expectedTag at tagValue
                                  change payload.val = expectedPayload.val at payloadValue
                                  have unitEq : unitWord = expectedUnit := Fin.ext unitValue
                                  have payloadEq : payload = expectedPayload :=
                                    Fin.ext payloadValue
                                  subst unitWord
                                  subst tag
                                  subst payload
                                  rfl

/-- The rejected scan branch packs the designated unit and no early factor. -/
theorem sampler_parameterValue_of_none {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (prepared : RSA.prepareResidueFromBits N (modulusBits N)
      residueProposalCount sample = RSA.prepareResidue N none) :
    (parameterValue input sample).first.toNat = 1 ∧
      (parameterValue input sample).second.first.toBool = false ∧
        (parameterValue input sample).second.second.toNat = 0 := by
  let _ : Fact (1 < N) := ⟨input.modulus_gt_one⟩
  have unitValue : (parameterValue input sample).first.toNat = 1 := by
    calc
      (parameterValue input sample).first.toNat =
          ((RSA.prepareResidueFromBits N (modulusBits N)
            residueProposalCount sample).unit : ZMod N).val :=
        parameterValue_unit_toNat input sample
      _ = ((RSA.prepareResidue N none).unit : ZMod N).val := by rw [prepared]
      _ = 1 := by
        have oneVal : ((1 : ZMod N)).val = 1 := ZMod.val_one N
        simpa only [RSA.prepareResidue_none_unit, Units.val_one] using oneVal
  have earlyNone : (RSA.prepareResidueFromBits N (modulusBits N)
      residueProposalCount sample).earlyFactor = none := by
    rw [prepared]
    exact RSA.prepareResidue_none_earlyFactor N
  have zeroWordNat : (CShape.wordOfNat (modulusBits N) 0).toNat = 0 := by
    simp only [CShape.wordOfNat_val, Nat.zero_mod]
  refine ⟨unitValue, parameterValue_earlyFactor_none input sample earlyNone, ?_⟩
  simpa only [parameterValue, earlyNone, CShape.Value.second] using zeroWordNat

/-- A selected coprime residue packs that residue as the circuit unit and no
early factor. -/
theorem sampler_parameterValue_of_coprime {N candidate : Nat}
    (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (prepared : RSA.prepareResidueFromBits N (modulusBits N)
      residueProposalCount sample = RSA.prepareResidue N (some candidate))
    (candidateBelow : candidate < N) (coprime : Nat.Coprime candidate N) :
    (parameterValue input sample).first.toNat = candidate ∧
      (parameterValue input sample).second.first.toBool = false ∧
        (parameterValue input sample).second.second.toNat = 0 := by
  let _ : Fact (1 < N) := ⟨input.modulus_gt_one⟩
  have unitValue : (parameterValue input sample).first.toNat = candidate := by
    calc
      (parameterValue input sample).first.toNat =
          ((RSA.prepareResidueFromBits N (modulusBits N)
            residueProposalCount sample).unit : ZMod N).val :=
        parameterValue_unit_toNat input sample
      _ = ((RSA.prepareResidue N (some candidate)).unit : ZMod N).val := by
        rw [prepared]
      _ = ((ZMod.unitOfCoprime candidate coprime : (ZMod N)ˣ) : ZMod N).val := by
        rw [RSA.prepareResidue_some_unit_of_coprime N candidate coprime]
      _ = candidate := by
        rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
        exact Nat.mod_eq_of_lt candidateBelow
  have earlyNone : (RSA.prepareResidueFromBits N (modulusBits N)
      residueProposalCount sample).earlyFactor = none := by
    rw [prepared]
    exact RSA.prepareResidue_some_earlyFactor_of_coprime N candidate coprime
  have zeroWordNat : (CShape.wordOfNat (modulusBits N) 0).toNat = 0 := by
    simp only [CShape.wordOfNat_val, Nat.zero_mod]
  refine ⟨unitValue, parameterValue_earlyFactor_none input sample earlyNone, ?_⟩
  simpa only [parameterValue, earlyNone, CShape.Value.second] using zeroWordNat

/-- A selected nonunit residue leaves the seeded unit in place and packs the
actual Euclidean GCD in the early-factor payload. -/
theorem sampler_parameterValue_of_not_coprime {N candidate : Nat}
    (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (prepared : RSA.prepareResidueFromBits N (modulusBits N)
      residueProposalCount sample = RSA.prepareResidue N (some candidate))
    (candidatePositive : 0 < candidate) (candidateBelow : candidate < N)
    (notCoprime : ¬ Nat.Coprime candidate N) :
    (parameterValue input sample).first.toNat = 1 ∧
      (parameterValue input sample).second.first.toBool = true ∧
        (parameterValue input sample).second.second.toNat = Nat.gcd candidate N := by
  let _ : Fact (1 < N) := ⟨input.modulus_gt_one⟩
  have traceNotOne :
      (NumberTheory.euclideanGCDTrace candidate N).value ≠ 1 := by
    rw [NumberTheory.euclideanGCDTrace_value]
    exact notCoprime
  have unitValue : (parameterValue input sample).first.toNat = 1 := by
    calc
      (parameterValue input sample).first.toNat =
          ((RSA.prepareResidueFromBits N (modulusBits N)
            residueProposalCount sample).unit : ZMod N).val :=
        parameterValue_unit_toNat input sample
      _ = ((RSA.prepareResidue N (some candidate)).unit : ZMod N).val := by
        rw [prepared]
      _ = (1 : ZMod N).val := by
        simp only [RSA.prepareResidue, RSA.prepareResidueExecution]
        rw [dif_neg traceNotOne]
        rfl
      _ = 1 := ZMod.val_one N
  have earlySome : (RSA.prepareResidueFromBits N (modulusBits N)
      residueProposalCount sample).earlyFactor = some (Nat.gcd candidate N) := by
    rw [prepared]
    exact RSA.prepareResidue_some_earlyFactor_of_not_coprime N candidate
      candidatePositive candidateBelow notCoprime
  rcases parameterValue_earlyFactor_some input sample earlySome with
    ⟨tagValue, payloadValue⟩
  exact ⟨unitValue, tagValue, payloadValue⟩

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler
