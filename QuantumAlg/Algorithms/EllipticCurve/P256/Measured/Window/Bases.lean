/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.FullRange.Seed.Chronological
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Order

/-!
# The same doubled rows in the original chronological addend family

All seventeen generator rows precede all seventeen inverse-target rows.
Each stream uses logical row sixteen down to zero. The complete unsigned
digit multiplies that same doubled base in the same original curve group,
including digit zero. No selected finite representative or truncated
subgroup scalar is substituted for the original branch-dependent addend.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

noncomputable section

open PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.P256.Measured.FullRange

private lemma groupPoint_pow_toMathlib {modulus : Nat}
    (curve : PrimeFieldShortWeierstrass modulus) (point : GroupPoint curve) (count : Nat) :
    letI : Fact modulus.Prime := ⟨curve.prime⟩
    (point ^ count).toMathlib = count • point.toMathlib := by
  let : Fact modulus.Prime := ⟨curve.prime⟩
  have same := map_pow (groupPointEquiv curve).mulEquiv point count
  change (point ^ count).toMathlib = count • point.toMathlib at same
  exact same

private lemma groupPoint_inv_toMathlib {modulus : Nat}
    (curve : PrimeFieldShortWeierstrass modulus) (point : GroupPoint curve) :
    letI : Fact modulus.Prime := ⟨curve.prime⟩
    (point⁻¹).toMathlib = -point.toMathlib := by
  let : Fact modulus.Prime := ⟨curve.prime⟩
  have same := (groupPointEquiv curve).mulEquiv.map_inv point
  change (point⁻¹).toMathlib = -point.toMathlib at same
  exact same

/-- The first seventeen chronological addends use the same actual generator rows. -/
lemma chronologicalAddend_first_toMathlib (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 17) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    (chronologicalAddend I branch (position.castAdd 17)).toMathlib =
      chronologicalAddress I branch (position.castAdd 17) •
        ((2 ^ (16 * (Fin.rev position).val)) •
          (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib) := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  rw [chronologicalAddend, chronologicalRow_first, chronologicalAddress_first]
  simp only [windowAddend, ExceptionalOffsetAveraging.Window.addend,
    Fin.val_castAdd, (Fin.rev position).isLt, ↓reduceIte]
  rw [groupPoint_pow_toMathlib]
  change ((2 ^ 16) ^ (Fin.rev position).val *
      Nat.FixedWidth.Radix.digit (2 ^ 16) branch.1.val (Fin.rev position).val) •
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib = _
  rw [← pow_mul, mul_nsmul]

/-- The second seventeen chronological addends use the same actual inverse-target rows. -/
lemma chronologicalAddend_second_toMathlib (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) (position : Fin 17) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    (chronologicalAddend I branch (position.natAdd 17)).toMathlib =
      chronologicalAddress I branch (position.natAdd 17) •
        ((2 ^ (16 * (Fin.rev position).val)) • (-I.publicKey.toMathlib)) := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  rw [chronologicalAddend, chronologicalRow_second, chronologicalAddress_second]
  simp only [windowAddend, ExceptionalOffsetAveraging.Window.addend, Fin.val_natAdd]
  rw [if_neg (by omega), Nat.add_sub_cancel_left]
  rw [groupPoint_pow_toMathlib, groupPoint_inv_toMathlib]
  change ((2 ^ 16) ^ (Fin.rev position).val *
      Nat.FixedWidth.Radix.digit (2 ^ 16) branch.2.val (Fin.rev position).val) •
      (-I.publicKey.toMathlib) = _
  rw [← pow_mul, mul_nsmul]

end

end QuantumAlg.EllipticCurve.P256.Measured.Window
