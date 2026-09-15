/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Allocation
import all
  QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Encoding.Cascade.Resources
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation.Space

/-!
# Complete original-input resources with charged coordinate conversion

The actual complete prefix charges its original two preparations and retains
all finite result cells. The following converted cascade charges four native
coordinate multipliers and every measured point call. Actual initialization
and execution share the same complete peak, including all supplied exponents,
both coordinate words, fixed arithmetic work, selector and result cells.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Encoding

noncomputable section

open Execution MeasuredUncompute

/-- Actual converted execution paths correspond exactly across the allocated entry permutation. -/
def placedConvertedPathEquiv {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) :
    (convertedCascade E points order coefficient).Path ≃
      (placedConvertedCascade E points order coefficient).Path :=
  ContextPermutation.localPathEquiv (convertedCascade E points order coefficient)
    (convertedCascade_isLocal E points order coefficient)
    (Allocation.after p.size count) (Allocation.body_entries p.size count)

/-- Post-allocation placement preserves the exact chronological conversion and measured trace. -/
theorem placedConvertedCascade_eventTrace {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (path : (convertedCascade E points order coefficient).Path) :
    (placedConvertedCascade E points order coefficient).eventTrace
        (placedConvertedPathEquiv E points order coefficient path) =
      (convertedCascade E points order coefficient).eventTrace path :=
  ContextPermutation.localCircuit_eventTrace _ _ _ _ path

/-- Every native event-duration assignment is preserved by the actual entry permutation. -/
theorem placedConvertedCascade_depth_exact {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (duration : Resource.Event .quantum → Nat)
    (path : (convertedCascade E points order coefficient).Path) :
    (placedConvertedCascade E points order coefficient).depth duration
        (placedConvertedPathEquiv E points order coefficient path) =
      (convertedCascade E points order coefficient).depth duration path :=
  ContextPermutation.localCircuit_depth _ _ _ _ duration path

/-- The placed code charges every actual conversion and every prescribed measured point call. -/
theorem placedConvertedCascade_budget {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (path : (placedConvertedCascade E points order coefficient).Path) :
    (placedConvertedCascade E points order coefficient).resourcePool path ≤
      ResourcePool.scale 4 (MAU.Multiplication.Gidney.nativeBudget p.size) +
        ResourcePool.scale order.length (MeasuredPointAddition.events p.size) := by
  obtain ⟨original, rfl⟩ := (placedConvertedPathEquiv E points order coefficient).surjective path
  exact (ContextPermutation.localCircuit_resourcePool _ _ _ _ original).le.trans
    (convertedCascade_budget E points order coefficient original)

/-- Four conversions and all point calls retain their independent serial depth envelope. -/
theorem placedConvertedCascade_depth {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (path : (placedConvertedCascade E points order coefficient).Path) :
    (placedConvertedCascade E points order coefficient).depth (fun _ => 1) path ≤
      4 * MAU.Multiplication.Gidney.eventBound p.size +
        order.length * MeasuredPointAddition.depthBound p.size := by
  obtain ⟨original, rfl⟩ := (placedConvertedPathEquiv E points order coefficient).surjective path
  have depth := placedConvertedCascade_depth_exact E points order coefficient (fun _ => 1) original
  exact depth.le.trans (convertedCascade_depth E points order coefficient original)

/-- Actual placement retains the original complete resident capacity and all supplied exponents. -/
theorem placedConvertedCascade_resident {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (path : (placedConvertedCascade E points order coefficient).Path) :
    (placedConvertedCascade E points order coefficient).peakResidentSpace path =
      readySpace p.size count :=
  (ContextPermutation.localCircuit_peakResidentSpace _ _ _ path).trans
    (readyContext_resident_exact p.size count)

/-- Actual placement retains the original auxiliary ownership roles, including every result cell. -/
theorem placedConvertedCascade_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (path : (placedConvertedCascade E points order coefficient).Path) :
    (placedConvertedCascade E points order coefficient).peakAuxiliarySpace path =
      readySpace p.size count :=
  (ContextPermutation.localCircuit_peakAuxiliarySpace _ _ _ path).trans
    (readyContext_auxiliary_exact p.size count)

/-- Independent complete allowance for two preparations, four conversions and all point calls. -/
def convertedEventBudget (modulus count calls : Nat) : ResourcePool .quantum :=
  ResourcePool.ofList [(InPlacePreparation.preparation modulus).event,
    (BasisPreparation.zero (indexedLayout modulus.size count)).event] +
      (ResourcePool.scale 4 (MAU.Multiplication.Gidney.nativeBudget modulus.size) +
        ResourcePool.scale calls (MeasuredPointAddition.events modulus.size))

/-- Every complete actual path includes both charged preparations and every converted point call. -/
theorem convertedCircuit_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCircuit E points order coefficient).Path) :
    (convertedCircuit E points order coefficient).resourcePool path ≤
      convertedEventBudget p count order.length := by
  change ResourcePool.ofList ((Allocation.initializeWork p count).eventTrace path.1 ++
    (placedConvertedCascade E points order coefficient).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, Allocation.initialize_eventTrace]
  exact ResourcePool.add_mono le_rfl
    (placedConvertedCascade_budget E points order coefficient path.2)

/-- The full serial depth includes the two actual preparations before conversion and execution. -/
theorem convertedCircuit_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCircuit E points order coefficient).Path) :
    (convertedCircuit E points order coefficient).depth (fun _ => 1) path ≤
      2 + (4 * MAU.Multiplication.Gidney.eventBound p.size +
        order.length * MeasuredPointAddition.depthBound p.size) := by
  change (Allocation.initializeWork p count).depth (fun _ => 1) path.1 +
    (placedConvertedCascade E points order coefficient).depth (fun _ => 1) path.2 ≤ _
  rw [Allocation.initialize_depth]
  exact Nat.add_le_add_left (placedConvertedCascade_depth E points order coefficient path.2) 2

/-- Actual initialization and converted execution reach only the same complete resident peak. -/
theorem convertedCircuit_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCircuit E points order coefficient).Path) :
    (convertedCircuit E points order coefficient).peakResidentSpace path =
      readySpace p.size count := by
  refine (Circuit.peakResidentSpace_seq (Allocation.initializeWork p count)
    (placedConvertedCascade E points order coefficient) path).trans ?_
  rw [Allocation.initialize_resident, placedConvertedCascade_resident]
  exact SpacePool.max_eq_right le_rfl

/-- Both preparations and every later call share the same exact fixed-role auxiliary peak. -/
theorem convertedCircuit_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCircuit E points order coefficient).Path) :
    (convertedCircuit E points order coefficient).peakAuxiliarySpace path =
      readySpace p.size count := by
  refine (Circuit.peakAuxiliarySpace_seq (Allocation.initializeWork p count)
    (placedConvertedCascade E points order coefficient) path).trans ?_
  rw [Allocation.initialize_auxiliary, placedConvertedCascade_auxiliary]
  exact SpacePool.max_eq_right le_rfl

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
