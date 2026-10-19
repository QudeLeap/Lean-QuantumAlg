/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication
public import QuantumAlg.Util.EllipticCurve
import all QuantumAlg.Util.EllipticCurve
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# P-256 domain parameters

This module records the standard P-256 constants and the explicit certificates
needed by the generic elliptic-curve DLP and parameterized arithmetic layers.
The arithmetic width is derived from the field modulus; no definition in this
endpoint freezes a circuit subtree at 256 bits.

The constants follow NIST SP 800-186, Section 3.2.1.3.  Large primality,
nonsingularity, base-point, and subgroup-order facts remain visible input
certificates rather than being recomputed by the resource endpoint.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace P256
namespace DomainParameters

noncomputable section

/-- P-256 prime modulus `2^256 - 2^224 + 2^192 + 2^96 - 1`. -/
def primeModulus : Nat :=
  2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- P-256 subgroup order. -/
public def subgroupOrder : Nat :=
  115792089210356248762697446949407573529996955224135760342422259061068512044369

/-- P-256 cofactor. -/
def cofactor : Nat := 1

/-- P-256 short-Weierstrass `b` coefficient as a natural number. -/
def coefficientBNat : Nat :=
  41058363725152142129326129780047268409114441015993725554835256314039467401291

/-- P-256 base-point `x` coordinate as a natural number. -/
def basePointXNat : Nat :=
  48439561293906451759052585252797914202762949526041747995844080717082404635286

/-- P-256 base-point `y` coordinate as a natural number. -/
def basePointYNat : Nat :=
  36134250956749795798585127919587881956611106672985015071877198253568414405109

/-- Canonical binary field width derived from the P-256 modulus. -/
def fieldWidth : Nat :=
  Nat.clog 2 primeModulus

set_option exponentiation.threshold 260 in
/-- The derived P-256 field width is 256 bits. -/
lemma fieldWidth_eq_256 : fieldWidth = 256 := by
  change Nat.clog 2 primeModulus = 256
  have h256 : (256 : Nat) = 16 * 16 := by norm_num
  have h255 : (255 : Nat) = 15 * 16 + 15 := by norm_num
  apply Nat.le_antisymm
  · apply Nat.clog_le_of_le_pow
    rw [h256, pow_mul]
    norm_num [primeModulus]
  · have hpower : 2 ^ 255 < primeModulus := by
      rw [h255, pow_add, pow_mul]
      norm_num [primeModulus]
    have hclog : 255 < Nat.clog 2 primeModulus :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).2 hpower
    exact Nat.succ_le_iff.mpr hclog

set_option exponentiation.threshold 260 in
/-- The standard modulus fits strictly inside its derived binary carrier. -/
lemma primeModulus_lt_capacity : primeModulus < 2 ^ fieldWidth := by
  rw [fieldWidth_eq_256, show (256 : Nat) = 16 * 16 by norm_num, pow_mul]
  norm_num [primeModulus]

/-- The standard modulus represented in the parameterized arithmetic word. -/
def modulusWord : PlainAdder.Word fieldWidth :=
  primeModulus

/-- The natural modulus seen by the parameterized elliptic-curve arithmetic. -/
public def fieldModulus : Nat :=
  modulusWord.val

/-- The derived arithmetic modulus is exactly the standard P-256 prime. -/
@[simp] lemma fieldModulus_eq_primeModulus :
    fieldModulus = primeModulus := by
  unfold fieldModulus modulusWord
  exact ZMod.val_natCast_of_lt primeModulus_lt_capacity

/-- The P-256 field has characteristic greater than three. -/
lemma three_lt_fieldModulus : 3 < fieldModulus := by
  rw [fieldModulus_eq_primeModulus]
  norm_num [primeModulus]

/-- The recorded P-256 cofactor has its standard value. -/
lemma cofactor_eq_one : cofactor = 1 := rfl

/-- P-256 short-Weierstrass `a` coefficient. -/
public def coefficientA : ZMod fieldModulus :=
  -3

/-- P-256 short-Weierstrass `b` coefficient in the prime field. -/
public def coefficientB : ZMod fieldModulus :=
  coefficientBNat

/-- P-256 base-point `x` coordinate in the prime field. -/
public def basePointX : ZMod fieldModulus :=
  basePointXNat

/-- P-256 base-point `y` coordinate in the prime field. -/
public def basePointY : ZMod fieldModulus :=
  basePointYNat

/-- Certificate that the recorded constants define the promised nonsingular
short-Weierstrass curve over the P-256 prime field. -/
public structure CurveCertificate where
  /-- The standard P-256 modulus is prime. -/
  prime : fieldModulus.Prime
  /-- The recorded short-Weierstrass equation is nonsingular. -/
  nonsingular :
    (4 : ZMod fieldModulus) * coefficientA ^ 3 +
        (27 : ZMod fieldModulus) * coefficientB ^ 2 ≠ 0

/-- Parameterized modular-arithmetic data derived from the certified modulus. -/
@[implicit_reducible]
def arithmeticParameters (cert : CurveCertificate) :
    PrimeFieldShortWeierstrass.Arithmetic.VariableModularMul.Parameters where
  width := fieldWidth
  widthPos := by rw [fieldWidth_eq_256]; norm_num
  modulus := modulusWord
  one_lt_modulus := (by norm_num : 1 < 3).trans three_lt_fieldModulus
  modulusPos := lt_trans (by norm_num) three_lt_fieldModulus
  modulusOdd := by
    exact cert.prime.odd_of_ne_two
      (ne_of_gt ((by norm_num : 2 < 3).trans three_lt_fieldModulus))

/-- The standard P-256 short-Weierstrass curve. -/
public def curve (cert : CurveCertificate) :
    PrimeFieldShortWeierstrass fieldModulus where
  prime := cert.prime
  three_lt := three_lt_fieldModulus
  a := coefficientA
  b := coefficientB
  nonsingular := cert.nonsingular

/-- Certificate that the standard affine base-point coordinates form a
nonsingular point of the certified P-256 curve. -/
public structure BasePointCertificate (cert : CurveCertificate) where
  nonsingular :
    (curve cert).toWeierstrassCurve.toAffine.Nonsingular
      basePointX basePointY

/-- The standard P-256 base point in the actual affine group carrier. -/
public def basePoint (cert : CurveCertificate)
    (baseCert : BasePointCertificate cert) :
    PrimeFieldShortWeierstrass.AffinePoint (curve cert) where
  x := basePointX
  y := basePointY
  nonsingular := baseCert.nonsingular

/-- Certificate for the advertised prime-order subgroup generated by the
standard base point. -/
public structure SubgroupCertificate (cert : CurveCertificate)
    (baseCert : BasePointCertificate cert) where
  /-- The recorded subgroup order is prime. -/
  prime : subgroupOrder.Prime
  /-- The advertised subgroup order is the actual order of the base point. -/
  subgroupOrder_eq_orderOf :
    subgroupOrder = orderOf (basePoint cert baseCert).toGroupPoint

/-- The certified subgroup order is positive. -/
lemma SubgroupCertificate.positive
    {cert : CurveCertificate} {baseCert : BasePointCertificate cert}
    (subgroupCert : SubgroupCertificate cert baseCert) :
    0 < subgroupOrder :=
  subgroupCert.prime.pos

/-- Public P-256 ECDLP instance.  It contains only public curve and subgroup
data plus the standard subgroup promise; no private scalar is problem data. -/
public structure PublicKeyInstance where
  /-- Certificate for the standard P-256 curve constants. -/
  curveCert : CurveCertificate
  /-- Certificate for the standard affine base point. -/
  baseCert : BasePointCertificate curveCert
  /-- Certificate for the standard prime-order subgroup. -/
  subgroupCert : SubgroupCertificate curveCert baseCert
  /-- Known nonidentity public key point `Q`. -/
  publicKey : PrimeFieldShortWeierstrass.AffinePoint (curve curveCert)
  /-- The public key lies in the cyclic subgroup generated by the base point. -/
  publicKey_mem_span :
    ∃ scalar : ZMod subgroupOrder,
      (basePoint curveCert baseCert).toGroupPoint ^ scalar.val =
        publicKey.toGroupPoint

namespace PublicKeyInstance

/-- Convert the P-256 interface to the generic actual-group ECDLP instance. -/
def toECDLPInstance (I : PublicKeyInstance) :
    PrimeFieldShortWeierstrass.ECDLPInstance (curve I.curveCert) where
  subgroupOrder := subgroupOrder
  subgroupOrder_pos := I.subgroupCert.positive
  subgroupOrder_prime := I.subgroupCert.prime
  basePoint := basePoint I.curveCert I.baseCert
  targetPoint := I.publicKey
  subgroupOrder_eq_orderOf := I.subgroupCert.subgroupOrder_eq_orderOf
  target_mem_span := I.publicKey_mem_span

end PublicKeyInstance

end

end DomainParameters
end P256
end EllipticCurve
end QuantumAlg

end
