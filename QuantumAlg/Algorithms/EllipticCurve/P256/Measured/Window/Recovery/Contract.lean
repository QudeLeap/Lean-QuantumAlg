/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Contract

/-!
# The original bounded public equation at the actual 260-bit result width

These are mathematical specifications and equality transports. The secret is
used only to identify accepted answers in a proof; no executable run is selected.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Recovery

noncomputable section

open PrimeFieldShortWeierstrass FiniteCyclicDLP
open FiniteCyclicDLP.Canonical.Probability (SecretInput residueIndex)

/-- Only the original bounded subgroup scalar satisfying the public equation is accepted. -/
def AcceptedOutput (I : DomainParameters.PublicKeyInstance)
    (output : CShape.Value (.option (.unsignedWord 260))) : Prop :=
  ∃ scalar : ZMod (Cascade.ecdlpInstance I).subgroupOrder,
    (Cascade.ecdlpInstance I).CandidateScalar scalar ∧
      output = .optionSome (CShape.wordOfNat 260 scalar.val)

private lemma accepted_width_cast {p : Nat} (E : PrimeFieldShortWeierstrass p)
    (original : ECDLPInstance E) {width : Nat}
    (same : orderWidth (ECDLP.Canonical.problem original) = width)
    (output : CShape.Value
      (.option (.unsignedWord (orderWidth (ECDLP.Canonical.problem original))))) :
    (∃ scalar : ZMod original.subgroupOrder, original.CandidateScalar scalar ∧
      cast (congrArg (fun n => CShape.Value (.option (.unsignedWord n))) same) output =
        .optionSome (CShape.wordOfNat width scalar.val)) ↔
      LogicalResources.AcceptedOutput E original output := by
  cases same
  rfl

/-- Transporting only the proved word width preserves the original acceptance relation. -/
lemma acceptedOutput_width_cast (I : DomainParameters.PublicKeyInstance)
    (output : CShape.Value (.option (.unsignedWord (Cascade.exponentWidth I)))) :
    AcceptedOutput I
      (cast (congrArg (fun n => CShape.Value (.option (.unsignedWord n)))
        (Cascade.exponentWidth_eq_260 I)) output) ↔
      LogicalResources.AcceptedOutput (DomainParameters.curve I.curveCert)
        (Cascade.ecdlpInstance I) output :=
  accepted_width_cast (DomainParameters.curve I.curveCert) (Cascade.ecdlpInstance I)
    (Cascade.exponentWidth_eq_260 I) output

/-- A bounded natural scalar satisfying the original point check is exactly the secret. -/
lemma bounded_scalar_eq_secret (I : DomainParameters.PublicKeyInstance)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (scalar : Nat) (bounded : scalar < (Cascade.ecdlpInstance I).subgroupOrder)
    (equation : let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
      scalar • (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib =
        I.publicKey.toMathlib) : scalar = input.secret.val := by
  let : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  exact (ECDLP.Measured.bounded_groupScalar_eq_target_iff
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) input scalar bounded).mp equation

/-- Exact scalar equality gives the actual 260-bit word, without modular truncation. -/
lemma bounded_word_eq_secret (I : DomainParameters.PublicKeyInstance)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (scalar : Nat) (bounded : scalar < (Cascade.ecdlpInstance I).subgroupOrder)
    (equation : let _ : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
      scalar • (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib =
        I.publicKey.toMathlib) :
    CShape.wordOfNat 260 scalar = CShape.wordOfNat 260 input.secret.val :=
  congrArg (CShape.wordOfNat 260) (bounded_scalar_eq_secret I input scalar bounded equation)

/-- The original acceptance relation identifies precisely the optional unique secret word. -/
lemma acceptedOutput_iff_secret (I : DomainParameters.PublicKeyInstance)
    (input : SecretInput (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)))
    (output : CShape.Value (.option (.unsignedWord 260))) :
    AcceptedOutput I output ↔ output = .optionSome (CShape.wordOfNat 260 input.secret.val) := by
  let : Fact DomainParameters.fieldModulus.Prime := ⟨I.curveCert.prime⟩
  constructor
  · rintro ⟨scalar, equation, result⟩
    have bounded : scalar.val < (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)).order :=
      (residueIndex (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) scalar).isLt
    have mathematical := (ECDLP.Measured.groupScalar_eq_target_iff
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) scalar.val).mpr equation
    have same := bounded_scalar_eq_secret I input scalar.val bounded mathematical
    simpa only [same] using result
  · intro result
    exact ⟨input.secret, input.target_eq_generator_pow, result⟩

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Recovery
