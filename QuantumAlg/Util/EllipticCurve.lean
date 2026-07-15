/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Util.ResidueEncoding
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Prime-field elliptic-curve model

This module records the quantum-free short-Weierstrass curve and affine
finite-point encoding conventions used by elliptic-curve circuit targets. The
definitions deliberately separate the mathematical curve model from later
reversible circuit realizations.  The ECDLP problem data follows the standard
prime-field elliptic-curve discrete-logarithm setup used by Proos--Zalka
[PZ03, ecc.tex:144-188] and the later resource-estimate presentation
[RNSL17, ECDLP.tex:129-194].
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve

/-- A short-Weierstrass curve `y^2 = x^3 + ax + b` over `ZMod p`, with the
prime-field and nonsingularity assumptions kept explicit. -/
structure PrimeFieldShortWeierstrass (p : ℕ) where
  /-- The field characteristic is prime. -/
  prime : p.Prime
  /-- Circuit targets use the short-Weierstrass form away from characteristics 2 and 3. -/
  three_lt : 3 < p
  /-- The `x` coefficient in `y^2 = x^3 + ax + b`. -/
  a : ZMod p
  /-- The constant coefficient in `y^2 = x^3 + ax + b`. -/
  b : ZMod p
  /-- Nonsingularity for the short-Weierstrass model. -/
  nonsingular : (4 : ZMod p) * a ^ 3 + (27 : ZMod p) * b ^ 2 ≠ 0

namespace PrimeFieldShortWeierstrass

variable {p n : ℕ} (E : PrimeFieldShortWeierstrass p)

/-- The corresponding Mathlib Weierstrass curve with `a₁=a₂=a₃=0`, `a₄=a`,
and `a₆=b`. -/
def toWeierstrassCurve : WeierstrassCurve (ZMod p) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := E.a
  a₆ := E.b

/-- The affine equation for finite points on the short-Weierstrass curve. -/
def AffineEquation (x y : ZMod p) : Prop :=
  y ^ 2 = x ^ 3 + E.a * x + E.b

/-- The local affine equation agrees with Mathlib's Weierstrass equation for
the associated short-form curve. -/
theorem affineEquation_iff_mathlib_equation (x y : ZMod p) :
    E.toWeierstrassCurve.toAffine.Equation x y ↔ E.AffineEquation x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp [toWeierstrassCurve, AffineEquation]

/-- A finite affine point on the curve. The point at infinity is represented
separately by `Point.infinity`. -/
structure FinitePoint (E : PrimeFieldShortWeierstrass p) where
  /-- Affine `x` coordinate. -/
  x : ZMod p
  /-- Affine `y` coordinate. -/
  y : ZMod p
  /-- The coordinates satisfy the curve equation. -/
  equation : E.AffineEquation x y

namespace FinitePoint

/-- Coordinate extensionality for finite affine points. -/
theorem ext_coordinates {E : PrimeFieldShortWeierstrass p}
    (P Q : FinitePoint E) (hx : P.x = Q.x) (hy : P.y = Q.y) :
    P = Q := by
  cases P with
  | mk px py peq =>
      cases Q with
      | mk qx qy qeq =>
          cases hx
          cases hy
          congr

end FinitePoint

/-- Affine points plus the point at infinity. -/
inductive Point (E : PrimeFieldShortWeierstrass p) where
  /-- The point at infinity, used as the group identity in the mathematical model. -/
  | infinity
  /-- A finite affine point on the curve. -/
  | finite : FinitePoint E → Point E

namespace Point

/-- Predicate selecting the point at infinity. -/
def IsInfinity : Point E → Prop
  | infinity => True
  | finite _ => False

/-- Predicate selecting finite affine points. -/
def IsFinite : Point E → Prop
  | infinity => False
  | finite _ => True

end Point

namespace FinitePoint

/-- View a finite affine point as a point of the curve with infinity adjoined. -/
def toPoint (P : FinitePoint E) : Point E :=
  Point.finite P

end FinitePoint

/-- Mathlib's nonsingular affine point type for the associated Weierstrass curve.
This is the bridge to the established affine group-law API; the local `Point`
type stays as the lightweight circuit-target representation policy. -/
abbrev MathlibPoint : Type :=
  E.toWeierstrassCurve.toAffine.Point

/-- A finite-point encoding convention for affine curve points. The point at
infinity is intentionally outside this pair encoding and must be represented by
an explicit tag in later circuit layers if a target includes it. -/
structure PointEncoding (E : PrimeFieldShortWeierstrass p) (n : ℕ) where
  /-- Binary residue encoding shared by the two affine coordinates. -/
  coordinate : BinaryResidueEncoding p n

namespace PointEncoding

/-- Encode a finite affine point as the pair of canonical residue labels for
its coordinates. -/
def encodeFinite {E : PrimeFieldShortWeierstrass p}
    (encoding : PointEncoding E n) (P : FinitePoint E) :
    Fin (2 ^ n) × Fin (2 ^ n) :=
  (encoding.coordinate.encode P.x, encoding.coordinate.encode P.y)

/-- Decode only the coordinate pair of a finite-point encoding. The decoded
pair still needs the curve equation to become a `FinitePoint`. -/
def decodeFiniteCoordinates {E : PrimeFieldShortWeierstrass p}
    (encoding : PointEncoding E n)
    (xy : Fin (2 ^ n) × Fin (2 ^ n)) : ZMod p × ZMod p :=
  (encoding.coordinate.decode xy.1, encoding.coordinate.decode xy.2)

/-- A pair of labels is a valid finite-point encoding when both labels are
canonical residues and the decoded coordinates satisfy the curve equation. -/
def IsValidFiniteEncoding {E : PrimeFieldShortWeierstrass p}
    (encoding : PointEncoding E n)
    (xy : Fin (2 ^ n) × Fin (2 ^ n)) : Prop :=
  encoding.coordinate.IsValid xy.1 ∧
    encoding.coordinate.IsValid xy.2 ∧
    E.AffineEquation
      (encoding.coordinate.decode xy.1)
      (encoding.coordinate.decode xy.2)

/-- Encoded finite points are valid finite-point encodings. -/
theorem encodeFinite_isValid {E : PrimeFieldShortWeierstrass p}
    (encoding : PointEncoding E n) (P : FinitePoint E) :
    IsValidFiniteEncoding encoding (encodeFinite encoding P) := by
  constructor
  · exact encoding.coordinate.encode_isValid P.x
  constructor
  · exact encoding.coordinate.encode_isValid P.y
  · simpa [encodeFinite] using P.equation

/-- Equality of finite encodings implies equality of affine coordinates. -/
theorem encodeFinite_ext {E : PrimeFieldShortWeierstrass p}
    (encoding : PointEncoding E n)
    {P Q : FinitePoint E} (h : encodeFinite encoding P = encodeFinite encoding Q) :
    P.x = Q.x ∧ P.y = Q.y := by
  have hx :
      encoding.coordinate.encode P.x = encoding.coordinate.encode Q.x :=
    congrArg Prod.fst h
  have hy :
      encoding.coordinate.encode P.y = encoding.coordinate.encode Q.y :=
    congrArg Prod.snd h
  constructor
  · have hdecode := congrArg encoding.coordinate.decode hx
    simpa using hdecode
  · have hdecode := congrArg encoding.coordinate.decode hy
    simpa using hdecode

/-- The finite affine encoding is injective on curve points. -/
theorem encodeFinite_injective {E : PrimeFieldShortWeierstrass p}
    (encoding : PointEncoding E n) :
    Function.Injective (encodeFinite encoding) := by
  intro P Q h
  exact FinitePoint.ext_coordinates P Q
    (encodeFinite_ext encoding h).1
    (encodeFinite_ext encoding h).2

end PointEncoding

/-- An elliptic-curve discrete-logarithm instance over the selected finite
short-Weierstrass curve. The scalar-multiplication map is supplied as the
mathematical bridge to later finite-cyclic DLP endpoints; reversible circuit
implementations live in the primitive layer. -/
structure ECDLPInstance (E : PrimeFieldShortWeierstrass p) where
  /-- Order of the cyclic subgroup generated by the base point. -/
  subgroupOrder : ℕ
  /-- The subgroup order is positive. -/
  subgroupOrder_pos : 0 < subgroupOrder
  /-- Base point whose multiples define the subgroup. -/
  basePoint : FinitePoint E
  /-- Target point promised to lie in the subgroup generated by `basePoint`. -/
  targetPoint : FinitePoint E
  /-- Scalar multiplication by residues modulo the subgroup order. -/
  scalarMultiplication : ZMod subgroupOrder → FinitePoint E
  /-- Scalar one recovers the base point. -/
  scalar_one : scalarMultiplication 1 = basePoint
  /-- The target point lies in the image of the scalar-multiplication map. -/
  target_mem_span : ∃ m : ZMod subgroupOrder, scalarMultiplication m = targetPoint

namespace ECDLPInstance

/-- Candidate scalars for an elliptic-curve discrete-logarithm instance. -/
def CandidateScalar {E : PrimeFieldShortWeierstrass p}
    (I : ECDLPInstance E) (m : ZMod I.subgroupOrder) : Prop :=
  I.scalarMultiplication m = I.targetPoint

/-- The stored subgroup promise gives at least one candidate scalar. -/
theorem exists_candidateScalar {E : PrimeFieldShortWeierstrass p}
    (I : ECDLPInstance E) :
    ∃ m : ZMod I.subgroupOrder, CandidateScalar I m :=
  I.target_mem_span

end ECDLPInstance

end PrimeFieldShortWeierstrass

end EllipticCurve
end QuantumAlg
