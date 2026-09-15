/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Cascade
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Resources
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade.Resources

/-!
# Native costs of the actual converted measured cascade

Two inverse-coordinate multipliers precede the measured cascade and two
forward-coordinate multipliers follow it. Their actual native traces and
depth are charged alongside every point call. The complete resident and
auxiliary peaks remain one existing ready workspace, including for an empty
point schedule. No basis-support condition is used in these resource bounds.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open Execution MeasuredUncompute

/-- The actual native trace contains all four conversions around the measured point schedule. -/
theorem convertedCascade_eventTrace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCascade E points order coefficient).Path) :
    (convertedCascade E points order coefficient).eventTrace path =
      ((MAU.Multiplication.Gidney.program p.size (InPlaceTarget.modulusWord p)
          coefficient⁻¹).eventTrace ++
        (MAU.Multiplication.Gidney.program p.size (InPlaceTarget.modulusWord p)
          coefficient⁻¹).eventTrace) ++
      ((cascade E points order).eventTrace path.2.1 ++
        ((MAU.Multiplication.Gidney.program p.size (InPlaceTarget.modulusWord p)
            coefficient).eventTrace ++
          (MAU.Multiplication.Gidney.program p.size (InPlaceTarget.modulusWord p)
            coefficient).eventTrace)) := by
  change (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹).eventTrace
    path.1 ++ ((cascade E points order).eventTrace path.2.1 ++
      (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient).eventTrace path.2.2) = _
  rw [pairCircuit_eventTrace p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹ path.1,
    pairCircuit_eventTrace p.size count (InPlaceTarget.modulusWord p) coefficient path.2.2]

/-- Four actual coordinate multipliers and every actual point call meet independent budgets. -/
theorem convertedCascade_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCascade E points order coefficient).Path) :
    (convertedCascade E points order coefficient).resourcePool path ≤
      ResourcePool.scale 4 (MAU.Multiplication.Gidney.nativeBudget p.size) +
        ResourcePool.scale order.length (MeasuredPointAddition.events p.size) := by
  change ResourcePool.ofList
    ((pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹).eventTrace path.1 ++
      ((cascade E points order).eventTrace path.2.1 ++
        (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient).eventTrace
          path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  have bound := add_le_add
    (pairCircuit_budget p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹ path.1)
    (add_le_add (cascade_budget E points order path.2.1)
      (pairCircuit_budget p.size count (InPlaceTarget.modulusWord p) coefficient path.2.2))
  refine bound.trans_eq ?_
  simp only [ResourcePool.scale_succ, ResourcePool.scale_zero, add_zero]
  ac_rfl

/-- Unit-duration serial depth charges all four conversions as well as the full point schedule. -/
theorem convertedCascade_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCascade E points order coefficient).Path) :
    (convertedCascade E points order coefficient).depth (fun _ => 1) path ≤
      4 * MAU.Multiplication.Gidney.eventBound p.size +
        order.length * MeasuredPointAddition.depthBound p.size := by
  change (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹).depth
    (fun _ => 1) path.1 + ((cascade E points order).depth (fun _ => 1) path.2.1 +
      (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient).depth
        (fun _ => 1) path.2.2) ≤ _
  have before := pairCircuit_depth p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹ path.1
  have middle := cascade_depth E points order path.2.1
  have after := pairCircuit_depth p.size count (InPlaceTarget.modulusWord p) coefficient path.2.2
  omega

/-- Four conversions and all measured calls share the same complete resident peak. -/
theorem convertedCascade_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCascade E points order coefficient).Path) :
    (convertedCascade E points order coefficient).peakResidentSpace path =
      readySpace p.size count :=
  local_resident _ _ _ (convertedCascade_isLocal E points order coefficient) path

/-- Reusing the existing A word introduces no additional auxiliary bank or result cells. -/
theorem convertedCascade_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCascade E points order coefficient).Path) :
    (convertedCascade E points order coefficient).peakAuxiliarySpace path =
      readySpace p.size count :=
  local_auxiliary _ _ _ (convertedCascade_isLocal E points order coefficient) path

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
