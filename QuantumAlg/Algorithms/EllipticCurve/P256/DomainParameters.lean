/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.EllipticCurve.DLP
public import QuantumAlg.Algorithms.Factoring.Common

/-!
# P-256 domain parameters

This module records the standard P-256 domain-parameter interface used by
the scalar-recovery resource theorem.  The constants follow NIST SP 800-186,
Section 3.2.1.3; that standards source is PDF-only, so it is credited in
prose rather than as a TeX-line citation.
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve

namespace P256DomainParameters

/-- Bit-size attached to the P-256 prime-field modulus. -/
def bitSize : Nat := 256

/-- P-256 prime modulus
`2^256 - 2^224 + 2^192 + 2^96 - 1`. -/
def primeModulus : Nat :=
  2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- P-256 subgroup order. -/
def subgroupOrder : Nat :=
  115792089210356248762697446949407573529996955224135760342422259061068512044369

/-- P-256 cofactor. -/
def cofactor : Nat := 1

/-- P-256 short-Weierstrass `a` coefficient. -/
def coefficientA : ZMod primeModulus :=
  -3

/-- P-256 short-Weierstrass `b` coefficient, recorded as a natural number. -/
def coefficientBNat : Nat :=
  41058363725152142129326129780047268409114441015993725554835256314039467401291

/-- P-256 short-Weierstrass `b` coefficient in the prime field. -/
def coefficientB : ZMod primeModulus :=
  coefficientBNat

/-- P-256 base-point `x` coordinate, recorded as a natural number. -/
def basePointXNat : Nat :=
  48439561293906451759052585252797914202762949526041747995844080717082404635286

/-- P-256 base-point `y` coordinate, recorded as a natural number. -/
def basePointYNat : Nat :=
  36134250956749795798585127919587881956611106672985015071877198253568414405109

/-- P-256 base-point `x` coordinate in the prime field. -/
def basePointX : ZMod primeModulus :=
  basePointXNat

/-- P-256 base-point `y` coordinate in the prime field. -/
def basePointY : ZMod primeModulus :=
  basePointYNat

/-- Certificate that the recorded P-256 constants define the promised
short-Weierstrass prime-field curve.  The large primality and nonsingularity
facts are intentionally supplied as data rather than recomputed by the
resource theorem. -/
structure CurveCertificate where
  /-- The standard P-256 modulus is prime. -/
  prime : primeModulus.Prime
  /-- The standard P-256 modulus is outside characteristics two and three. -/
  three_lt : 3 < primeModulus
  /-- The standard P-256 short-Weierstrass equation is nonsingular. -/
  nonsingular :
    (4 : ZMod primeModulus) * coefficientA ^ 3 +
        (27 : ZMod primeModulus) * coefficientB ^ 2 ≠ 0

/-- The standard P-256 short-Weierstrass curve built from a certificate. -/
def curve (cert : CurveCertificate) :
    PrimeFieldShortWeierstrass primeModulus where
  prime := cert.prime
  three_lt := cert.three_lt
  a := coefficientA
  b := coefficientB
  nonsingular := cert.nonsingular

/-- Certificate that the recorded affine base-point coordinates lie on the
standard P-256 curve. -/
structure BasePointCertificate where
  /-- The standard base point satisfies the P-256 affine equation. -/
  equation :
    basePointY ^ 2 =
      basePointX ^ 3 + coefficientA * basePointX + coefficientB

/-- The standard P-256 base point as a finite affine curve point. -/
def basePoint (cert : CurveCertificate) (baseCert : BasePointCertificate) :
    PrimeFieldShortWeierstrass.FinitePoint (curve cert) where
  x := basePointX
  y := basePointY
  equation := by
    simpa [curve, PrimeFieldShortWeierstrass.AffineEquation]
      using baseCert.equation

/-- Certificate for the prime-order subgroup advertised by the P-256 domain
parameters. -/
structure SubgroupOrderCertificate where
  /-- The recorded subgroup order is positive. -/
  positive : 0 < subgroupOrder
  /-- The recorded subgroup order is prime. -/
  prime : subgroupOrder.Prime
  /-- The P-256 cofactor is one. -/
  cofactor_eq_one : cofactor = 1

/-- A natural-number private scalar in the standard range `0 <= m < r`, where
`r` is the P-256 subgroup order. -/
structure ScalarRangeWitness where
  /-- The natural-number representative of the private scalar. -/
  value : Nat
  /-- The representative is reduced modulo the P-256 subgroup order. -/
  value_lt_order : value < subgroupOrder

namespace ScalarRangeWitness

/-- View a range-certified scalar as an element of `ZMod r`. -/
def toZMod (scalar : ScalarRangeWitness) : ZMod subgroupOrder :=
  scalar.value

end ScalarRangeWitness

/-- Lean-facing interface for a P-256 ECDLP instance with public key
`Q = [m]P`.  The scalar-multiplication map is an abstract mathematical bridge:
primitive/circuit modules provide implementations, while this layer records the
standard curve inputs and the scalar-recovery promise. -/
structure ScalarRecoveryInterface where
  /-- Certificate for the standard P-256 curve constants. -/
  curveCert : CurveCertificate
  /-- Certificate that the standard base point lies on the curve. -/
  baseCert : BasePointCertificate
  /-- Certificate for the standard prime-order subgroup. -/
  subgroupCert : SubgroupOrderCertificate
  /-- Known public key point `Q`. -/
  publicKey :
    PrimeFieldShortWeierstrass.FinitePoint (curve curveCert)
  /-- Range-certified private scalar `m`. -/
  privateScalar : ScalarRangeWitness
  /-- Abstract scalar multiplication by residues modulo the subgroup order. -/
  scalarMultiplication :
    ZMod subgroupOrder ->
      PrimeFieldShortWeierstrass.FinitePoint (curve curveCert)
  /-- Multiplication by one returns the standard base point `P`. -/
  scalar_one :
    scalarMultiplication 1 = basePoint curveCert baseCert
  /-- The public key is the standard scalar multiple `Q = [m]P`. -/
  publicKey_eq_scalar_mul :
    scalarMultiplication privateScalar.toZMod = publicKey

namespace ScalarRecoveryInterface

/-- Convert the P-256 scalar-recovery interface to the generic prime-field
ECDLP instance interface. -/
def toECDLPInstance (I : ScalarRecoveryInterface) :
    PrimeFieldShortWeierstrass.ECDLPInstance (curve I.curveCert) where
  subgroupOrder := subgroupOrder
  subgroupOrder_pos := I.subgroupCert.positive
  basePoint := basePoint I.curveCert I.baseCert
  targetPoint := I.publicKey
  scalarMultiplication := I.scalarMultiplication
  scalar_one := I.scalar_one
  target_mem_span := ⟨I.privateScalar.toZMod, I.publicKey_eq_scalar_mul⟩

/-- The stored private scalar is a candidate scalar for the induced ECDLP
instance. -/
theorem privateScalar_candidate (I : ScalarRecoveryInterface) :
    I.toECDLPInstance.CandidateScalar I.privateScalar.toZMod := by
  simpa [toECDLPInstance, PrimeFieldShortWeierstrass.ECDLPInstance.CandidateScalar]
    using I.publicKey_eq_scalar_mul

/-- The scalar-recovery interface records the natural-number scalar range
required by the public P-256 statement. -/
theorem privateScalar_lt_order (I : ScalarRecoveryInterface) :
    I.privateScalar.value < subgroupOrder :=
  I.privateScalar.value_lt_order

end ScalarRecoveryInterface

end P256DomainParameters

end EllipticCurve
end QuantumAlg
