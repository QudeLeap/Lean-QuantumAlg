/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Util.ResidueEncoding
public import Mathlib.Algebra.Field.ZMod
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

section

namespace QuantumAlg
namespace EllipticCurve

/-- A short-Weierstrass curve `y^2 = x^3 + ax + b` over `ZMod p`, with the
prime-field and nonsingularity assumptions kept explicit. -/
public structure PrimeFieldShortWeierstrass (p : ℕ) where
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
public def toWeierstrassCurve : WeierstrassCurve (ZMod p) where
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
lemma affineEquation_iff_mathlib_equation (x y : ZMod p) :
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
lemma ext_coordinates {E : PrimeFieldShortWeierstrass p}
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
public abbrev MathlibPoint : Type :=
  E.toWeierstrassCurve.toAffine.Point

/-- Multiplicative wrapper around Mathlib's affine elliptic-curve group.  The
curve stored in the type supplies the prime-field instance internally, so
downstream ECDLP statements use the actual group law without an additional
`Fact p.Prime` assumption. -/
public structure GroupPoint (E : PrimeFieldShortWeierstrass p) where
  /-- Underlying Mathlib point, including the point at infinity. -/
  toMathlib : E.MathlibPoint
deriving DecidableEq

/-- The representation equivalence used to transport Mathlib's additive group
law to the multiplicative convention expected by finite-cyclic DLP. -/
public def groupPointEquiv (E : PrimeFieldShortWeierstrass p) :
    GroupPoint E ≃ Multiplicative E.MathlibPoint where
  toFun := fun P => Multiplicative.ofAdd P.toMathlib
  invFun := fun P => ⟨Multiplicative.toAdd P⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- Actual elliptic-curve group structure, transported from Mathlib. -/
public noncomputable instance instGroupGroupPoint (E : PrimeFieldShortWeierstrass p) :
    Group (GroupPoint E) := by
  letI : Fact p.Prime := ⟨E.prime⟩
  exact (groupPointEquiv E).group

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
lemma encodeFinite_isValid {E : PrimeFieldShortWeierstrass p}
    (encoding : PointEncoding E n) (P : FinitePoint E) :
    IsValidFiniteEncoding encoding (encodeFinite encoding P) := by
  constructor
  · exact encoding.coordinate.encode_isValid P.x
  constructor
  · exact encoding.coordinate.encode_isValid P.y
  · simpa [encodeFinite] using P.equation

/-- Equality of finite encodings implies equality of affine coordinates. -/
lemma encodeFinite_ext {E : PrimeFieldShortWeierstrass p}
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
lemma encodeFinite_injective {E : PrimeFieldShortWeierstrass p}
    (encoding : PointEncoding E n) :
    Function.Injective (encodeFinite encoding) := by
  intro P Q h
  exact FinitePoint.ext_coordinates P Q
    (encodeFinite_ext encoding h).1
    (encodeFinite_ext encoding h).2

end PointEncoding

/-- A nonsingular finite affine point on the selected prime-field curve.  This
is the canonical finite-point carrier shared by the mathematical ECDLP model
and the reusable circuit layer. -/
public structure AffinePoint (E : PrimeFieldShortWeierstrass p) where
  /-- Affine `x` coordinate over the prime field. -/
  x : ZMod p
  /-- Affine `y` coordinate over the prime field. -/
  y : ZMod p
  /-- Nonsingularity proof for the coordinate pair on the selected curve. -/
  nonsingular : E.toWeierstrassCurve.toAffine.Nonsingular x y
deriving DecidableEq

noncomputable instance instFintypeAffinePoint
    (E : PrimeFieldShortWeierstrass p) [NeZero p] :
    Fintype (AffinePoint E) := by
  classical
  let e :
      AffinePoint E ≃
        {xy : ZMod p × ZMod p //
          E.toWeierstrassCurve.toAffine.Nonsingular xy.1 xy.2} := {
    toFun := fun P => ⟨(P.x, P.y), P.nonsingular⟩
    invFun := fun P => { x := P.1.1, y := P.1.2, nonsingular := P.2 }
    left_inv := by
      intro P
      cases P
      rfl
    right_inv := by
      intro P
      rcases P with ⟨xy, hxy⟩
      rcases xy with ⟨x, y⟩
      rfl
  }
  exact Fintype.ofEquiv
    {xy : ZMod p × ZMod p //
      E.toWeierstrassCurve.toAffine.Nonsingular xy.1 xy.2} e.symm

namespace AffinePoint

/-- Coordinate extensionality for finite affine points. -/
lemma ext_coordinates {E : PrimeFieldShortWeierstrass p}
    (P Q : AffinePoint E) (hx : P.x = Q.x) (hy : P.y = Q.y) :
    P = Q := by
  cases P with
  | mk px py pnonsingular =>
      cases Q with
      | mk qx qy qnonsingular =>
          cases hx
          cases hy
          congr

/-- View a finite affine point as Mathlib's nonsingular affine point. -/
public def toMathlib {E : PrimeFieldShortWeierstrass p} (P : AffinePoint E) :
    E.MathlibPoint :=
  .some P.x P.y P.nonsingular

/-- View a finite affine point in the actual multiplicative elliptic-curve
group used by the finite-cyclic DLP reduction. -/
public def toGroupPoint {E : PrimeFieldShortWeierstrass p} (P : AffinePoint E) :
    GroupPoint E :=
  ⟨P.toMathlib⟩

/-- Forget the nonsingularity witness and keep the finite-point equation. -/
def toFinitePoint {E : PrimeFieldShortWeierstrass p} (P : AffinePoint E) :
    FinitePoint E where
  x := P.x
  y := P.y
  equation := (E.affineEquation_iff_mathlib_equation P.x P.y).mp P.nonsingular.1

/-- View a finite affine point as the finite branch of the lightweight curve
point type. -/
def toCurvePoint {E : PrimeFieldShortWeierstrass p} (P : AffinePoint E) :
    Point E :=
  P.toFinitePoint.toPoint

@[simp] lemma toCurvePoint_isFinite {E : PrimeFieldShortWeierstrass p}
    (P : AffinePoint E) :
    Point.IsFinite E P.toCurvePoint :=
  trivial

@[simp] lemma toCurvePoint_not_infinity {E : PrimeFieldShortWeierstrass p}
    (P : AffinePoint E) :
    ¬ Point.IsInfinity E P.toCurvePoint := by
  simp [toCurvePoint, FinitePoint.toPoint, Point.IsInfinity]

/-- Encode a finite affine point by its canonical residue coordinates. -/
def encode {E : PrimeFieldShortWeierstrass p} {n : ℕ}
    (encoding : PointEncoding E n) (P : AffinePoint E) :
    Fin (2 ^ n) × Fin (2 ^ n) :=
  encoding.encodeFinite P.toFinitePoint

lemma encode_isValid {E : PrimeFieldShortWeierstrass p} {n : ℕ}
    (encoding : PointEncoding E n) (P : AffinePoint E) :
    encoding.IsValidFiniteEncoding (P.encode encoding) :=
  encoding.encodeFinite_isValid P.toFinitePoint

lemma decodeFiniteCoordinates_encode
    {E : PrimeFieldShortWeierstrass p} {n : ℕ}
    (encoding : PointEncoding E n) (P : AffinePoint E) :
    encoding.decodeFiniteCoordinates (P.encode encoding) = (P.x, P.y) := by
  simp [encode, PointEncoding.decodeFiniteCoordinates,
    PointEncoding.encodeFinite, toFinitePoint]

lemma encode_ext {E : PrimeFieldShortWeierstrass p} {n : ℕ}
    (encoding : PointEncoding E n) {P Q : AffinePoint E}
    (h : P.encode encoding = Q.encode encoding) :
    P.x = Q.x ∧ P.y = Q.y :=
  encoding.encodeFinite_ext h

lemma encode_injective {E : PrimeFieldShortWeierstrass p} {n : ℕ}
    (encoding : PointEncoding E n) :
    Function.Injective (fun P : AffinePoint E => P.encode encoding) := by
  intro P Q h
  exact ext_coordinates P Q (encode_ext encoding h).1 (encode_ext encoding h).2

end AffinePoint

/-- An elliptic-curve discrete-logarithm instance over the selected finite
short-Weierstrass curve.  Its subgroup and target promises are stated directly
in the actual Mathlib elliptic-curve group; reversible circuit implementations
remain in the primitive layer. -/
public structure ECDLPInstance (E : PrimeFieldShortWeierstrass p) where
  /-- Order of the cyclic subgroup generated by the base point. -/
  subgroupOrder : ℕ
  /-- The subgroup order is positive. -/
  subgroupOrder_pos : 0 < subgroupOrder
  /-- The public ECDLP subgroup order is prime. -/
  subgroupOrder_prime : subgroupOrder.Prime
  /-- Base point whose multiples define the subgroup. -/
  basePoint : AffinePoint E
  /-- Target point promised to lie in the subgroup generated by `basePoint`. -/
  targetPoint : AffinePoint E
  /-- The declared subgroup order is the actual order of the base point. -/
  subgroupOrder_eq_orderOf :
    subgroupOrder = orderOf basePoint.toGroupPoint
  /-- The target lies in the actual cyclic subgroup generated by the base. -/
  target_mem_span :
    ∃ m : ZMod subgroupOrder,
      basePoint.toGroupPoint ^ m.val = targetPoint.toGroupPoint

namespace ECDLPInstance

/-- Candidate scalars for an elliptic-curve discrete-logarithm instance. -/
def CandidateScalar {E : PrimeFieldShortWeierstrass p}
    (I : ECDLPInstance E) (m : ZMod I.subgroupOrder) : Prop :=
  I.basePoint.toGroupPoint ^ m.val = I.targetPoint.toGroupPoint

/-- The stored subgroup promise gives at least one candidate scalar. -/
lemma exists_candidateScalar {E : PrimeFieldShortWeierstrass p}
    (I : ECDLPInstance E) :
    ∃ m : ZMod I.subgroupOrder, CandidateScalar I m :=
  I.target_mem_span

end ECDLPInstance

end PrimeFieldShortWeierstrass

end EllipticCurve
end QuantumAlg

end
