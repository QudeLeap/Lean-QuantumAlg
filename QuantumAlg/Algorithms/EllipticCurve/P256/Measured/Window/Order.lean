/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.EllipticCurve.Order
import all QuantumAlg.Algorithms.EllipticCurve.P256.Cascade.Parameters
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Coordinates.Bases.Order

/-!
# Original subgroup orders for both chronological window-base families

The original public-key certificates supply the generator and target orders.
Negating the same target preserves its order, and every actual power-of-two
base retains that order. The standard subgroup order contains both original
window widths. These mathematical facts do not prepare a classical base port
or replace the required actual negative-target source value.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

noncomputable section

open PrimeFieldShortWeierstrass
open ClassicalRoutines.EllipticCurve.WindowTables

/-- The original generator has its certified subgroup order in the same additive group. -/
lemma basePoint_addOrderOf (I : DomainParameters.PublicKeyInstance) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    addOrderOf (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib =
      DomainParameters.subgroupOrder := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  exact (affinePoint_addOrderOf_eq_orderOf _ _).trans (Cascade.basePoint_orderOf I)

/-- The original affine public target has the same prime subgroup order. -/
lemma targetPoint_addOrderOf (I : DomainParameters.PublicKeyInstance) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    addOrderOf I.publicKey.toMathlib = DomainParameters.subgroupOrder := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  exact (affinePoint_addOrderOf_eq_orderOf _ _).trans (Cascade.targetPoint_orderOf I)

/-- The second family's same inverse target retains the original subgroup order. -/
lemma inverseTarget_addOrderOf (I : DomainParameters.PublicKeyInstance) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    addOrderOf (-I.publicKey.toMathlib) = DomainParameters.subgroupOrder := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  rw [addOrderOf_neg]
  exact targetPoint_addOrderOf I

private lemma subgroupOrder_large : 3 < DomainParameters.subgroupOrder := by
  norm_num [DomainParameters.subgroupOrder]

/-- Every original generator row retains the subgroup order, without reducing its scalar. -/
lemma baseRow_addOrderOf (I : DomainParameters.PublicKeyInstance) (row : Nat) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    addOrderOf ((2 ^ (16 * row)) •
      (DomainParameters.basePoint I.curveCert I.baseCert).toMathlib) =
      DomainParameters.subgroupOrder := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  exact pow_two_nsmul_addOrderOf _ _ _ I.subgroupCert.prime subgroupOrder_large
    (basePoint_addOrderOf I)

/-- Every same inverse-target row retains the subgroup order on the original public-key domain. -/
lemma inverseTargetRow_addOrderOf (I : DomainParameters.PublicKeyInstance) (row : Nat) :
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    addOrderOf ((2 ^ (16 * row)) • (-I.publicKey.toMathlib)) =
      DomainParameters.subgroupOrder := by
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  exact pow_two_nsmul_addOrderOf _ _ _ I.subgroupCert.prime subgroupOrder_large
    (inverseTarget_addOrderOf I)

/-- Both original full and tail row capacities fit strictly below the same subgroup order. -/
lemma windowTableFits (width : Nat) (bounded : width ≤ 15) :
    2 ^ (width + 1) < DomainParameters.subgroupOrder := by
  have within : 2 ^ (width + 1) ≤ 2 ^ 16 :=
    Nat.pow_le_pow_right Nat.zero_lt_two (by omega)
  exact within.trans_lt (by norm_num [DomainParameters.subgroupOrder])

end

end QuantumAlg.EllipticCurve.P256.Measured.Window
