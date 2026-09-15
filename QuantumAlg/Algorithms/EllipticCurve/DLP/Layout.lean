/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Layout.Curve
import QuantumAlg.Init
import all QuantumAlg.Util.EllipticCurve
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.Classical.EllipticCurve
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
public import QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
public import QuantumAlg.Util.EllipticCurve

/-!
# Intrinsic prime-field ECDLP workspace layout

The opaque group-action oracle acts on two Fourier exponent registers followed
by one real elliptic-curve point register.  The point register is not supplied
by the caller: it is the canonical identity-inclusive layout consisting of one
infinity tag and two fixed-width field coordinates.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ECDLP
namespace Canonical
namespace Layout

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

namespace FixedEC

/-- Identity-inclusive fixed-width point code. -/
abbrev Code := ClassicalAlgorithms.EllipticCurve.Code

end FixedEC

/-- One identity-inclusive raw point code. -/
abbrev PointCode (E : PrimeFieldShortWeierstrass p) : Type :=
  FixedEC.Code (fieldWidth E)

/-- Product view used to obtain the exact tag-plus-coordinate binary layout. -/
abbrev RawPointCode (E : PrimeFieldShortWeierstrass p) : Type :=
  Bool × (Fin (2 ^ fieldWidth E) × Fin (2 ^ fieldWidth E))

/-- Fieldwise equivalence between the named point code and its product layout. -/
def pointCodeEquiv (E : PrimeFieldShortWeierstrass p) :
    PointCode E ≃ RawPointCode E where
  toFun := fun code => (code.tag, (code.x, code.y))
  invFun := fun raw =>
    { tag := raw.1
      x := raw.2.1
      y := raw.2.2 }
  left_inv := by
    intro code
    cases code
    rfl
  right_inv := by
    rintro ⟨tag, x, y⟩
    rfl

/-- Physical binary encoding of the identity-inclusive point code. -/
def pointCodeEncoding (E : PrimeFieldShortWeierstrass p) :
    BinaryLabelEncoding (PointCode E) :=
  (BinaryLabelEncoding.prod BinaryLabelEncoding.bool
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.finIdentity (fieldWidth E))
      (BinaryLabelEncoding.finIdentity (fieldWidth E)))).relabel
        (pointCodeEquiv E)

/-- Exact point-register width: one infinity tag and two field coordinates. -/
public def pointWidth (E : PrimeFieldShortWeierstrass p) : Nat :=
  1 + 2 * fieldWidth E

@[simp] theorem pointCodeEncoding_width (E : PrimeFieldShortWeierstrass p) :
    (pointCodeEncoding E).width = pointWidth E := by
  simp [pointCodeEncoding, pointWidth]
  omega

/-- Canonical identity-inclusive code of one actual elliptic-curve group
point. -/
def pointCode (E : PrimeFieldShortWeierstrass p) (point : GroupPoint E) :
    PointCode E :=
  ClassicalAlgorithms.EllipticCurve.encode (curveSpec E) point.toMathlib

/-- The intrinsic point code is injective, including at the group identity. -/
theorem pointCode_injective (E : PrimeFieldShortWeierstrass p) :
    Function.Injective (pointCode E) := by
  intro left right encoded
  rcases left with ⟨left⟩
  rcases right with ⟨right⟩
  have pointEq :=
    (ClassicalAlgorithms.EllipticCurve.encode_injective
      (curveSpec E)) encoded
  cases pointEq
  rfl

/-- Faithful computational-basis encoding of the actual elliptic-curve group
carrier. -/
def pointEncoding (E : PrimeFieldShortWeierstrass p) :
    BinaryLabelEncoding (GroupPoint E) where
  width := pointWidth E
  encode := fun point =>
    ⟨(pointCodeEncoding E).encode (pointCode E point), by
      simpa [pointCodeEncoding_width] using
        ((pointCodeEncoding E).encode (pointCode E point)).isLt⟩
  encode_injective := by
    intro left right encoded
    apply pointCode_injective E
    apply (pointCodeEncoding E).encode_injective
    exact Fin.ext (Fin.mk.inj encoded)

@[simp] theorem pointEncoding_width (E : PrimeFieldShortWeierstrass p) :
    (pointEncoding E).width = pointWidth E :=
  rfl

/-- Full basis encoding: two exponent registers followed by the intrinsic
elliptic-curve point register. -/
def fullEncoding (I : ECDLPInstance E) :
    BinaryLabelEncoding
      ((Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I)) ×
          Fin (2 ^ FiniteCyclicDLP.orderWidth (problem I))) × GroupPoint E) :=
  BinaryLabelEncoding.prod
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.finIdentity (FiniteCyclicDLP.orderWidth (problem I)))
      (BinaryLabelEncoding.finIdentity (FiniteCyclicDLP.orderWidth (problem I))))
    (pointEncoding E)

/-- Exact logical width of the real three-register ECDLP experiment. -/
public abbrev totalQubits (I : ECDLPInstance E) : Nat :=
  FiniteCyclicDLP.orderWidth (problem I) +
    FiniteCyclicDLP.orderWidth (problem I) + pointWidth E

@[simp] theorem fullEncoding_width (I : ECDLPInstance E) :
    (fullEncoding I).width = totalQubits I := by
  simp [fullEncoding, totalQubits]

/-- The prime-order subgroup embeds into the intrinsic point register. -/
theorem subgroupOrder_le_point_capacity (I : ECDLPInstance E) :
    I.subgroupOrder ≤ 2 ^ pointWidth E := by
  let orbit : Fin I.subgroupOrder → Fin (2 ^ pointWidth E) := fun index =>
    (pointEncoding E).encode (I.basePoint.toGroupPoint ^ index.val)
  have orbitInjective : Function.Injective orbit := by
    intro left right encoded
    apply Fin.ext
    exact pow_injOn_Iio_orderOf
      (I.subgroupOrder_eq_orderOf ▸ left.isLt)
      (I.subgroupOrder_eq_orderOf ▸ right.isLt)
      ((pointEncoding E).encode_injective encoded)
  simpa [orbit] using Fintype.card_le_of_injective orbit orbitInjective

/-- The oversampled exponent width is at most four bits beyond the intrinsic
point width. -/
theorem orderWidth_le_pointWidth_add_four (I : ECDLPInstance E) :
    FiniteCyclicDLP.orderWidth (problem I) ≤ pointWidth E + 4 := by
  apply Nat.clog_le_of_le_pow
  change 12 * I.subgroupOrder ≤ 2 ^ (pointWidth E + 4)
  calc
    12 * I.subgroupOrder ≤ 16 * I.subgroupOrder := by omega
    _ ≤ 16 * 2 ^ pointWidth E :=
      Nat.mul_le_mul_left 16 (subgroupOrder_le_point_capacity I)
    _ = 2 ^ (pointWidth E + 4) := by
      simp [pow_add, Nat.mul_comm]

/-- Explicit linear-in-field-width logical-qubit ceiling underlying the public
`O(log p)` claim. -/
theorem totalQubits_le_three_mul_pointWidth_add_eight
    (I : ECDLPInstance E) :
    totalQubits I ≤ 3 * pointWidth E + 8 := by
  unfold totalQubits
  have widthBound := orderWidth_le_pointWidth_add_four I
  omega

/-- Fully expanded coordinate-width form of the same logical-qubit ceiling. -/
theorem totalQubits_le_eleven_add_six_mul_fieldWidth
    (I : ECDLPInstance E) :
    totalQubits I ≤ 11 + 6 * fieldWidth E := by
  have bound := totalQubits_le_three_mul_pointWidth_add_eight I
  unfold pointWidth at bound
  omega

end

end Layout
end Canonical
end ECDLP
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
