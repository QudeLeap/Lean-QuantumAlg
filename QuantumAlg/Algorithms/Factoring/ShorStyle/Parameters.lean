/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.Common
import all QuantumAlg.Core.Algorithm.ClassicalOp
import all QuantumAlg.Util.RSA.ResidueSampling

/-!
# Public widths and deterministic residue parameters for Shor factoring

This module owns the source widths, admissible modulus, retry calibration,
finite parameter shape and exact deterministic decoding of an already chosen
sample. It defines no execution or oracle. Native sampling must write these
same finite values from its actual random-bit instruction.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical

noncomputable section

/-- Number of bits in the public modulus register. -/
def modulusBits (N : Nat) : Nat := Nat.clog 2 N

/-- Doubled phase-register width used by the source order-finding theorem
[Sho95, source.tex:1183-1245]. -/
def phaseBits (N : Nat) : Nat := 2 * modulusBits N

/-- Number of fixed-width proposals decoded by one internal sampler. -/
def residueProposalCount : Nat := 16

/-- Exact number of uniformly sampled bits in one attempt. -/
@[implicit_reducible] public def residueSamplingBits (N : Nat) : Nat :=
  residueProposalCount * modulusBits N

/-- Public executable assumptions for a known nontrivial modulus. -/
public structure Input (N : Nat) : Prop where
  modulus_gt_one : 1 < N

theorem Input.modulus_ge_two {N : Nat} (input : Input N) : 2 ≤ N :=
  input.modulus_gt_one

theorem Input.modulus_pos {N : Nat} (input : Input N) : 0 < N :=
  Nat.zero_lt_of_lt input.modulus_gt_one

theorem Input.neZero {N : Nat} (input : Input N) : NeZero N :=
  ⟨Nat.ne_of_gt input.modulus_pos⟩

theorem Input.modulusBits_pos {N : Nat} (input : Input N) :
    0 < modulusBits N :=
  Nat.clog_pos (by norm_num : 1 < 2) input.modulus_gt_one

theorem Input.register_fits {N : Nat} (_input : Input N) :
    N ≤ 2 ^ modulusBits N :=
  Nat.le_pow_clog (by norm_num : 1 < 2) N

theorem Input.registerSquare_fits {N : Nat} (input : Input N) :
    N ^ 2 ≤ 2 ^ phaseBits N := by
  calc
    N ^ 2 ≤ (2 ^ modulusBits N) ^ 2 :=
      Nat.pow_le_pow_left input.register_fits 2
    _ = 2 ^ (modulusBits N * 2) := (pow_mul 2 (modulusBits N) 2).symm
    _ = 2 ^ phaseBits N := by rw [phaseBits, Nat.mul_comm]

/-- One-attempt inverse-polynomial success denominator. -/
def sourceSuccessDenominator (N : Nat) : Nat := 48 * modulusBits N

/-- Certified complement of the one-attempt success floor. -/
def sourceFailureBudget (N : Nat) : FailureBudget where
  failureNumerator := sourceSuccessDenominator N - 1
  failureDenominator := sourceSuccessDenominator N

theorem sourceFailureBudget_strictlyWellFormed {N : Nat} (input : Input N) :
    (sourceFailureBudget N).StrictlyWellFormed := by
  have positive : 0 < sourceSuccessDenominator N := by
    exact Nat.mul_pos (by norm_num) input.modulusBits_pos
  have greaterThanOne : 1 < sourceSuccessDenominator N := by
    have bitsPositive := input.modulusBits_pos
    unfold sourceSuccessDenominator
    omega
  refine
    { toWellFormed :=
        { numerator_pos := ?_
          denominator_pos := positive
          numerator_le_denominator := by
            simp only [sourceFailureBudget]
            omega }
      numerator_lt_denominator := by
        simp only [sourceFailureBudget]
        omega }
  simp only [sourceFailureBudget]
  omega

/-- Exact retry count driven only by the caller's failure parameter. -/
def retryCount (N : Nat) (budget : FailureBudget) : Nat :=
  FailureBudget.retryCountFor (sourceFailureBudget N) budget

theorem retryCount_pos (N : Nat) (budget : FailureBudget) :
    0 < retryCount N budget :=
  FailureBudget.retryCountFor_pos (sourceFailureBudget N) budget

/-- Runtime parameter retained beside one sampled terminal outcome. -/
def ParameterShape (width : Nat) : CShape :=
  .product (.unsignedWord width)
    (.product .bit (.unsignedWord width))

/-- Encode the sealed RSA preparation in the runtime parameter shape. -/
def parameterValue {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    CShape.Value (ParameterShape (modulusBits N)) :=
  let : NeZero N := input.neZero
  let prepared := RSA.prepareResidueFromBits N (modulusBits N)
    residueProposalCount sample
  let unitValue : Fin (2 ^ modulusBits N) :=
    ⟨(prepared.unit : ZMod N).val,
      lt_of_lt_of_le (ZMod.val_lt (prepared.unit : ZMod N))
        input.register_fits⟩
  let factorValue : CShape.Value
      (.product .bit (.unsignedWord (modulusBits N))) :=
    match prepared.earlyFactor with
    | none => .product (.bit false) (CShape.wordOfNat (modulusBits N) 0)
    | some factor =>
        .product (.bit true) (CShape.wordOfNat (modulusBits N) factor)
  .product (.unsignedWord unitValue) factorValue

@[simp] theorem parameterValue_unit_toNat {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) :
    (parameterValue input sample).first.toNat =
      (((RSA.prepareResidueFromBits N (modulusBits N)
        residueProposalCount sample).unit : ZMod N).val) := by
  simp [parameterValue, CShape.Value.first, CShape.Value.toNat]

theorem parameterValue_earlyFactor_none {N : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (noneFound : (RSA.prepareResidueFromBits N (modulusBits N)
      residueProposalCount sample).earlyFactor = none) :
    (parameterValue input sample).second.first.toBool = false := by
  simp [parameterValue, noneFound, CShape.Value.second, CShape.Value.first,
    CShape.Value.toBool]

theorem parameterValue_earlyFactor_some {N factor : Nat} (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (found : (RSA.prepareResidueFromBits N (modulusBits N)
      residueProposalCount sample).earlyFactor = some factor) :
    (parameterValue input sample).second.first.toBool = true ∧
      (parameterValue input sample).second.second.toNat = factor := by
  have factorLt : factor < N :=
    (RSA.prepareResidueFromBits N (modulusBits N)
      residueProposalCount sample).earlyFactor_sound factor found |>.2.2
  have factorFits : factor < CShape.wordModulus (modulusBits N) :=
    factorLt.trans_le input.register_fits
  simp [parameterValue, found, CShape.Value.second, CShape.Value.first,
    CShape.Value.toBool, CShape.wordOfNat_val,
    Nat.mod_eq_of_lt factorFits]

end

end QuantumAlg.Factoring.ShorStyle.Canonical
