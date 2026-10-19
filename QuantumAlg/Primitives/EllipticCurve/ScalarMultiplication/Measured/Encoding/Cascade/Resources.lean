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
lemma convertedCascade_eventTrace {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCascade E points order coefficient
      allowAllocation).Path) :
    (convertedCascade E points order coefficient allowAllocation).eventTrace path =
      ((MAU.Multiplication.Gidney.program p.size (InPlaceTarget.modulusWord p)
          coefficient⁻¹).eventTrace ++
        (MAU.Multiplication.Gidney.program p.size (InPlaceTarget.modulusWord p)
          coefficient⁻¹).eventTrace) ++
      ((cascade E points order allowAllocation).eventTrace path.2.1 ++
        ((MAU.Multiplication.Gidney.program p.size (InPlaceTarget.modulusWord p)
            coefficient).eventTrace ++
          (MAU.Multiplication.Gidney.program p.size (InPlaceTarget.modulusWord p)
            coefficient).eventTrace)) := by
  change (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹
    allowAllocation).eventTrace
    path.1 ++ ((cascade E points order allowAllocation).eventTrace path.2.1 ++
      (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient
        allowAllocation).eventTrace path.2.2) = _
  rw [pairCircuit_eventTrace (allowAllocation := allowAllocation) p.size count
    (InPlaceTarget.modulusWord p) coefficient⁻¹ path.1,
    pairCircuit_eventTrace (allowAllocation := allowAllocation) p.size count
      (InPlaceTarget.modulusWord p) coefficient path.2.2]

/-- Four actual coordinate multipliers and every actual point call meet independent budgets. -/
lemma convertedCascade_budget {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCascade E points order coefficient
      allowAllocation).Path) :
    (convertedCascade E points order coefficient allowAllocation).resourcePool path ≤
      ResourcePool.scale 4 (MAU.Multiplication.Gidney.nativeBudget p.size) +
        ResourcePool.scale order.length (MeasuredPointAddition.events p.size) := by
  change ResourcePool.ofList
    ((pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹
      allowAllocation).eventTrace path.1 ++
      ((cascade E points order allowAllocation).eventTrace path.2.1 ++
        (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient
          allowAllocation).eventTrace
          path.2.2)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append]
  have bound := add_le_add
    (pairCircuit_budget (allowAllocation := allowAllocation) p.size count (InPlaceTarget.modulusWord
      p) coefficient⁻¹ path.1)
    (add_le_add (cascade_budget (allowAllocation := allowAllocation) E points order path.2.1)
      (pairCircuit_budget (allowAllocation := allowAllocation) p.size count
        (InPlaceTarget.modulusWord p) coefficient path.2.2))
  refine bound.trans_eq ?_
  simp only [ResourcePool.scale_succ, ResourcePool.scale_zero, add_zero]
  ac_rfl

/-- Unit-duration serial depth charges all four conversions as well as the full point schedule. -/
lemma convertedCascade_depth {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCascade E points order coefficient
      allowAllocation).Path) :
    (convertedCascade E points order coefficient allowAllocation).depth (fun _ => 1) path ≤
      4 * MAU.Multiplication.Gidney.eventBound p.size +
        order.length * MeasuredPointAddition.depthBound p.size := by
  change (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹
    allowAllocation).depth
    (fun _ => 1) path.1 + ((cascade E points order allowAllocation).depth (fun _ => 1) path.2.1 +
      (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient allowAllocation).depth
        (fun _ => 1) path.2.2) ≤ _
  have before := pairCircuit_depth (allowAllocation := allowAllocation) p.size count
    (InPlaceTarget.modulusWord p) coefficient⁻¹ path.1
  have middle := cascade_depth (allowAllocation := allowAllocation) E points order path.2.1
  have after := pairCircuit_depth (allowAllocation := allowAllocation) p.size count
    (InPlaceTarget.modulusWord p) coefficient path.2.2
  omega

/-- Four conversions and all measured calls share the same complete resident peak. -/
lemma convertedCascade_resident {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCascade E points order coefficient
      allowAllocation).Path) :
    (convertedCascade E points order coefficient allowAllocation).peakResidentSpace path =
      readySpace p.size count := by
  change ((pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹
    allowAllocation).seq ((cascade E points order allowAllocation).seq
      (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient
        allowAllocation))).peakResidentSpace path = _
  have before := pairCircuit_resident (allowAllocation := allowAllocation) p.size count
    (InPlaceTarget.modulusWord p) coefficient⁻¹ path.1
  have middle := cascade_resident (allowAllocation := allowAllocation) E points order path.2.1
  have after := pairCircuit_resident (allowAllocation := allowAllocation) p.size count
    (InPlaceTarget.modulusWord p) coefficient path.2.2
  have tail := (Circuit.peakResidentSpace_seq
    (cascade E points order allowAllocation)
    (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient allowAllocation)
    path.2).trans
      ((congrArg₂ SpacePool.max middle after).trans (SpacePool.max_self _))
  exact (Circuit.peakResidentSpace_seq
    (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹ allowAllocation)
    ((cascade E points order allowAllocation).seq
      (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient allowAllocation))
    path).trans ((congrArg₂ SpacePool.max before tail).trans (SpacePool.max_self _))

/-- Reusing the existing A word introduces no additional auxiliary bank or result cells. -/
lemma convertedCascade_auxiliary {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCascade E points order coefficient
      allowAllocation).Path) :
    (convertedCascade E points order coefficient allowAllocation).peakAuxiliarySpace path =
      readySpace p.size count := by
  change ((pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹
    allowAllocation).seq ((cascade E points order allowAllocation).seq
      (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient
        allowAllocation))).peakAuxiliarySpace path = _
  have before := pairCircuit_auxiliary (allowAllocation := allowAllocation) p.size count
    (InPlaceTarget.modulusWord p) coefficient⁻¹ path.1
  have middle := cascade_auxiliary (allowAllocation := allowAllocation) E points order path.2.1
  have after := pairCircuit_auxiliary (allowAllocation := allowAllocation) p.size count
    (InPlaceTarget.modulusWord p) coefficient path.2.2
  have tail := (Circuit.peakAuxiliarySpace_seq
    (cascade E points order allowAllocation)
    (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient allowAllocation)
    path.2).trans
      ((congrArg₂ SpacePool.max middle after).trans (SpacePool.max_self _))
  exact (Circuit.peakAuxiliarySpace_seq
    (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient⁻¹ allowAllocation)
    ((cascade E points order allowAllocation).seq
      (pairCircuit p.size count (InPlaceTarget.modulusWord p) coefficient allowAllocation))
    path).trans ((congrArg₂ SpacePool.max before tail).trans (SpacePool.max_self _))

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
