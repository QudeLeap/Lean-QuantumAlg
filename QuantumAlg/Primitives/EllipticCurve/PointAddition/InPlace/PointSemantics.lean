/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Mathematics

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Basic
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.InPlace.Semantics

/-!
# Point semantics of the compact in-place schedule

This module identifies the field words emitted by the literal seventeen-stage
schedule with ordinary short-Weierstrass affine addition.  The extra reverse
domain is exactly the nonzero denominator required by the schedule's second
inversion cleanup.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace GenericPointAddition
namespace InPlace
namespace PointSemantics

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth

/-- The literal schedule's arithmetic certificate follows from its forward
and reverse affine domains. -/
lemma cleanCertificate_of_domains
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (hpOdd : Odd p) (hfull : 2 ^ (fieldTail.succ - 1) ≤ p)
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (control : Bool) (P Q : AffinePoint E)
    (hforward : GenericAddDomain P Q)
    (hreverse : control = true →
      GenericAddDomain (genericAddPoint E P Q hforward) Q) :
    Schedule.CleanCertificate fieldTail counterTail p hpPos hp hfit
      (Semantics.montgomeryInput fieldTail p hpPos hp control
        P.x P.y Q.x Q.y) := by
  apply Semantics.montgomeryInput_cleanCertificate fieldTail counterTail p
    hpPos hp hfit hcapacity hwidth hcounterWidth hpOdd hfull
  · exact sub_ne_zero.mpr hforward
  · exact secondDenominator_ne_zero_of_domains E control P Q hforward hreverse

/-- The same native program whose resources are counted implements controlled
affine addition on a clean Montgomery-encoded basis state. -/
lemma program_applyNormalized_point_ket
    (fieldTail counterTail p : Nat)
    (hpPos : 0 < p) (hp : p < 2 ^ fieldTail.succ)
    (hfit : counterTail.succ ≤ fieldTail.succ)
    (hcapacity : fieldTail.succ ≤ 2 ^ (counterTail + 1))
    (hwidth : counterTail + 2 ≤ fieldTail.succ)
    (hcounterWidth : counterTail + 2 = Nat.clog 2 (2 * fieldTail.succ))
    (hpOdd : Odd p) (hfull : 2 ^ (fieldTail.succ - 1) ≤ p)
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (control : Bool) (P Q : AffinePoint E)
    (hforward : GenericAddDomain P Q)
    (hreverse : control = true →
      GenericAddDomain (genericAddPoint E P Q hforward) Q) :
    let point := selectedPoint E control P Q hforward
    (Resources.program fieldTail counterTail p hpPos hp hfit hcapacity hwidth
        (Semantics.montgomeryWord fieldTail p hpPos hp Q.x)
        (Semantics.montgomeryWord fieldTail p hpPos hp Q.y)).applyNormalized environment
        (NormalizedVector.ket
          ((QubitLayout.canonical
              (Layout.encoding fieldTail.succ (counterTail + 2)).width).basisEquiv.symm
            ((Layout.encoding fieldTail.succ (counterTail + 2)).encode
              (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
                control (Semantics.montgomeryWord fieldTail p hpPos hp P.y) 0
                ⟨p, hp⟩
                (Semantics.montgomeryWord fieldTail p hpPos hp P.x) 0)))) =
      NormalizedVector.ket
        ((QubitLayout.canonical
            (Layout.encoding fieldTail.succ (counterTail + 2)).width).basisEquiv.symm
          ((Layout.encoding fieldTail.succ (counterTail + 2)).encode
            (MontgomeryOperations.cleanState fieldTail.succ (counterTail + 2)
              control (Semantics.montgomeryWord fieldTail p hpPos hp point.y) 0
              ⟨p, hp⟩
              (Semantics.montgomeryWord fieldTail p hpPos hp point.x) 0))) := by
  dsimp only
  let data := Semantics.montgomeryInput fieldTail p hpPos hp control
    P.x P.y Q.x Q.y
  have certificate := cleanCertificate_of_domains fieldTail counterTail p
    hpPos hp hfit hcapacity hwidth hcounterWidth hpOdd hfull E control P Q
    hforward hreverse
  have action := Resources.program_applyNormalized_clean_ket (environment := environment)
    fieldTail
    counterTail p hpPos hp hfit hcapacity hwidth hcounterWidth data certificate
  have outputs := Semantics.montgomeryInput_outputs fieldTail counterTail p
    hpPos hp hfit hcapacity hwidth hcounterWidth hpOdd hfull control
    P.x P.y Q.x Q.y (sub_ne_zero.mpr hforward)
  have coordinates := selectedOutputs_eq_point E control P Q hforward
  rw [outputs.1, outputs.2, coordinates.1, coordinates.2] at action
  simpa [data, Semantics.montgomeryInput] using action

end
end PointSemantics
end InPlace
end GenericPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
