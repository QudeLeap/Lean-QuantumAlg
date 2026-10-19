/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
public import QuantumAlg.Algorithms.EllipticCurve.P256.DomainParameters
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
import all QuantumAlg.Algorithms.EllipticCurve.P256.DomainParameters
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.PrimeOrderTailBound.P256

/-!
# P-256 exponent and affine-addend parameters

The original certified public key determines the known-order group problem,
both oversampled exponent widths and the exact big-endian affine addends.
The first half contains generator powers and the second half inverse target
powers. Their nonidentity certificates use only the original prime subgroup
order and affine public-key promise. This mathematical schedule is independent
of a controlled-addition execution backend.
-/

namespace QuantumAlg.EllipticCurve.P256.Cascade

noncomputable section

open PrimeFieldShortWeierstrass

/-- Generic ECDLP instance induced by the certified P-256 public key. -/
public def ecdlpInstance (I : DomainParameters.PublicKeyInstance) :=
  I.toECDLPInstance

/-- Width of either oversampled P-256 exponent register. -/
def exponentWidth (I : DomainParameters.PublicKeyInstance) : Nat :=
  FiniteCyclicDLP.orderWidth
    (PrimeFieldShortWeierstrass.ECDLP.Canonical.problem (ecdlpInstance I))

/-- The parameterized order-width construction instantiates to 260. -/
lemma exponentWidth_eq_260 (I : DomainParameters.PublicKeyInstance) :
    exponentWidth I = 260 := by
  change Nat.clog 2 (12 * DomainParameters.subgroupOrder) = 260
  exact FiniteCyclicDLP.PrimeOrderTailBound.P256.exponentRegisterWidth_eq_260

/-- Every finite affine point represents a nonidentity group point. -/
lemma affinePoint_toGroupPoint_ne_one
    {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (point : AffinePoint E) : point.toGroupPoint ≠ 1 := by
  intro equality
  have underlying := congrArg GroupPoint.toMathlib equality
  change point.toMathlib = 0 at underlying
  exact WeierstrassCurve.Affine.Point.some_ne_zero
    point.nonsingular underlying

/-- A nonidentity group point has a canonical finite affine representative. -/
lemma exists_affineRepresentative
    {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (point : GroupPoint E) (nonidentity : point ≠ 1) :
    ∃ representative : AffinePoint E,
      representative.toGroupPoint = point := by
  rcases point with ⟨point⟩
  cases point with
  | zero =>
      exact False.elim (nonidentity rfl)
  | some x y nonsingular =>
      exact ⟨⟨x, y, nonsingular⟩, rfl⟩

/-- Selected affine representative of a certified nonidentity group point. -/
def affineRepresentative
    {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (point : GroupPoint E) (nonidentity : point ≠ 1) : AffinePoint E :=
  Classical.choose (exists_affineRepresentative point nonidentity)

/-- The selected affine representative denotes the original group point. -/
@[simp] lemma affineRepresentative_toGroupPoint
    {p : Nat} {E : PrimeFieldShortWeierstrass p}
    (point : GroupPoint E) (nonidentity : point ≠ 1) :
    (affineRepresentative point nonidentity).toGroupPoint = point :=
  Classical.choose_spec (exists_affineRepresentative point nonidentity)

/-- The base point has the advertised prime order. -/
lemma basePoint_orderOf (I : DomainParameters.PublicKeyInstance) :
    orderOf (ecdlpInstance I).basePoint.toGroupPoint =
      DomainParameters.subgroupOrder :=
  I.subgroupCert.subgroupOrder_eq_orderOf.symm

/-- The public target is a nonidentity group point because its stored
representation is affine. -/
lemma targetPoint_ne_one (I : DomainParameters.PublicKeyInstance) :
    (ecdlpInstance I).targetPoint.toGroupPoint ≠ 1 :=
  affinePoint_toGroupPoint_ne_one I.publicKey

/-- Any nonidentity element of the advertised prime-order subgroup has the
same order as the generator. -/
lemma targetPoint_orderOf (I : DomainParameters.PublicKeyInstance) :
    orderOf (ecdlpInstance I).targetPoint.toGroupPoint =
      DomainParameters.subgroupOrder := by
  rcases I.publicKey_mem_span with ⟨scalar, scalarSpec⟩
  have dividesBase :
      orderOf (ecdlpInstance I).targetPoint.toGroupPoint ∣
        orderOf (ecdlpInstance I).basePoint.toGroupPoint := by
    change orderOf I.publicKey.toGroupPoint ∣
      orderOf (DomainParameters.basePoint I.curveCert I.baseCert).toGroupPoint
    rw [← scalarSpec]
    exact orderOf_pow_dvd _
  rw [basePoint_orderOf I] at dividesBase
  rcases (Nat.dvd_prime I.subgroupCert.prime).mp dividesBase with
    orderOne | orderPrime
  · exact False.elim
      (targetPoint_ne_one I (orderOf_eq_one_iff.mp orderOne))
  · exact orderPrime

/-- A power of two cannot be divisible by the odd P-256 subgroup prime. -/
lemma powerOfTwo_ne_one_of_order_eq
    {G : Type*} [Group G] (I : DomainParameters.PublicKeyInstance) (point : G)
    (pointOrder : orderOf point = DomainParameters.subgroupOrder)
    (bit : Nat) : point ^ (2 ^ bit) ≠ 1 := by
  intro equality
  have dividesPower : DomainParameters.subgroupOrder ∣ 2 ^ bit := by
    rw [← pointOrder]
    exact orderOf_dvd_of_pow_eq_one equality
  have dividesTwo : DomainParameters.subgroupOrder ∣ 2 :=
    I.subgroupCert.prime.dvd_of_dvd_pow dividesPower
  have equalsTwo : DomainParameters.subgroupOrder = 2 :=
    (Nat.prime_dvd_prime_iff_eq I.subgroupCert.prime Nat.prime_two).mp
      dividesTwo
  norm_num [DomainParameters.subgroupOrder] at equalsTwo

/-- Big-endian exponent attached to physical control position `position`. -/
def bitExponent (t position : Nat) : Nat :=
  t - 1 - position

/-- Mathematical fixed addend selected by one of the `2t` controls. -/
def addendGroup (I : DomainParameters.PublicKeyInstance)
    (index : Fin (2 * exponentWidth I)) :
    GroupPoint (DomainParameters.curve I.curveCert) :=
  if index.val < exponentWidth I then
    (ecdlpInstance I).basePoint.toGroupPoint ^
      (2 ^ bitExponent (exponentWidth I) index.val)
  else
    ((ecdlpInstance I).targetPoint.toGroupPoint ^
      (2 ^ bitExponent (exponentWidth I)
        (index.val - exponentWidth I)))⁻¹

/-- Every scheduled addend is nonidentity, so it has an affine circuit
representation. -/
lemma addendGroup_ne_one (I : DomainParameters.PublicKeyInstance)
    (index : Fin (2 * exponentWidth I)) :
    addendGroup I index ≠ 1 := by
  unfold addendGroup
  split_ifs with left
  · exact powerOfTwo_ne_one_of_order_eq I _ (basePoint_orderOf I) _
  · simpa using inv_ne_one.mpr
      (powerOfTwo_ne_one_of_order_eq I _ (targetPoint_orderOf I) _)

/-- Affine fixed-addend schedule consumed by the literal ECADD cascade. -/
def addend (I : DomainParameters.PublicKeyInstance)
    (index : Fin (2 * exponentWidth I)) :
    AffinePoint (DomainParameters.curve I.curveCert) :=
  affineRepresentative (addendGroup I index) (addendGroup_ne_one I index)

/-- The affine schedule denotes the intended big-endian group powers. -/
@[simp] lemma addend_toGroupPoint (I : DomainParameters.PublicKeyInstance)
    (index : Fin (2 * exponentWidth I)) :
    (addend I index).toGroupPoint = addendGroup I index :=
  affineRepresentative_toGroupPoint _ _

end

end QuantumAlg.EllipticCurve.P256.Cascade
