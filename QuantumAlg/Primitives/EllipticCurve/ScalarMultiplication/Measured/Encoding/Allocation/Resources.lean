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
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# Complete original-input resources with charged coordinate conversion

The actual complete prefix charges all zero preparations and fixed X loads,
and retains all finite result cells. The following converted cascade charges four native
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
    (coefficient : (ZMod p)ˣ) (allowAllocation : Bool := true) :
    (convertedCascade E points order coefficient false).Path ≃
      (placedConvertedCascade E points order coefficient allowAllocation).Path :=
  Equiv.refl _

/-- Post-allocation placement preserves the exact chronological conversion and measured trace. -/
lemma placedConvertedCascade_eventTrace {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (path : (convertedCascade E points order coefficient false).Path) :
    (placedConvertedCascade E points order coefficient allowAllocation).eventTrace
        (placedConvertedPathEquiv E points order coefficient allowAllocation path) =
      (convertedCascade E points order coefficient false).eventTrace path := rfl

/-- Every native event-duration assignment is preserved by the actual entry permutation. -/
lemma placedConvertedCascade_depth_exact {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (path : (convertedCascade E points order coefficient false).Path) :
    (placedConvertedCascade E points order coefficient allowAllocation).depth duration
        (placedConvertedPathEquiv E points order coefficient allowAllocation path) =
      (convertedCascade E points order coefficient false).depth duration path := rfl

/-- The placed code charges every actual conversion and every prescribed measured point call. -/
lemma placedConvertedCascade_budget {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (path : (placedConvertedCascade E points order coefficient allowAllocation).Path) :
    (placedConvertedCascade E points order coefficient allowAllocation).resourcePool path ≤
      ResourcePool.scale 4 (MAU.Multiplication.Gidney.nativeBudget p.size) +
        ResourcePool.scale order.length (MeasuredPointAddition.events p.size) := by
  exact (Circuit.resourcePool_embed (allowAllocation := allowAllocation)
    (ContextEmbedding.alongPermutation (Allocation.body_entries p.size count))
    (convertedCascade E points order coefficient false) path).le.trans
      (convertedCascade_budget (allowAllocation := false) E points order coefficient path)

/-- Four conversions and all point calls retain their independent serial depth envelope. -/
lemma placedConvertedCascade_depth {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (path : (placedConvertedCascade E points order coefficient allowAllocation).Path) :
    (placedConvertedCascade E points order coefficient allowAllocation).depth (fun _ => 1) path ≤
      4 * MAU.Multiplication.Gidney.eventBound p.size +
        order.length * MeasuredPointAddition.depthBound p.size := by
  exact convertedCascade_depth (allowAllocation := false) E points order coefficient path

/-- Actual placement retains the original complete resident capacity and all supplied exponents. -/
lemma placedConvertedCascade_resident {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (path : (placedConvertedCascade E points order coefficient allowAllocation).Path) :
    (placedConvertedCascade E points order coefficient allowAllocation).peakResidentSpace path =
      readySpace p.size count :=
  (Circuit.peakResidentSpace_embed (allowAllocation := allowAllocation)
    (ContextEmbedding.alongPermutation (Allocation.body_entries p.size count))
    (convertedCascade E points order coefficient false) path).trans
      ((ContextPermutation.resident_space (Allocation.body_entries p.size count)).symm.trans
        (readyContext_resident_exact p.size count))

/-- Actual placement retains the original auxiliary ownership roles, including every result cell. -/
lemma placedConvertedCascade_auxiliary {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E)
    (order : List (Fin count)) (coefficient : (ZMod p)ˣ)
    (path : (placedConvertedCascade E points order coefficient allowAllocation).Path) :
    (placedConvertedCascade E points order coefficient allowAllocation).peakAuxiliarySpace path =
      readySpace p.size count :=
  (Circuit.peakAuxiliarySpace_embed (allowAllocation := allowAllocation)
    (ContextEmbedding.alongPermutation (Allocation.body_entries p.size count))
    (convertedCascade E points order coefficient false) path).trans
      ((ContextPermutation.auxiliary_space (Allocation.body_entries p.size count)).symm.trans
        (readyContext_auxiliary_exact p.size count))

/-- Actual input-determined preparation, four conversions and every point call. -/
def convertedEventBudget (modulus count calls : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ResourcePool.ofList (Allocation.initializationTrace modulus count) +
      (ResourcePool.scale 4 (MAU.Multiplication.Gidney.nativeBudget modulus.size) +
        ResourcePool.scale calls (MeasuredPointAddition.events modulus.size))

/-- Every complete path includes all preparation events and converted point calls. -/
lemma convertedCircuit_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCircuit E points order coefficient).Path) :
    (convertedCircuit E points order coefficient).resourcePool path ≤
      convertedEventBudget p count order.length := by
  change ResourcePool.ofList ((Allocation.initializeWork p count).eventTrace path.1 ++
    (placedConvertedCascade E points order coefficient).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, Allocation.initialize_eventTrace]
  exact ResourcePool.add_mono le_rfl
    (placedConvertedCascade_budget (allowAllocation := true) E points order coefficient path.2)

/-- The full serial depth includes all preparation and X-load dependencies. -/
lemma convertedCircuit_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCircuit E points order coefficient).Path) :
    (convertedCircuit E points order coefficient).depth (fun _ => 1) path ≤
      ResourcePool.weightedCount (fun _ => 1)
        (ResourcePool.ofList (Allocation.initializationTrace p count)) +
          (4 * MAU.Multiplication.Gidney.eventBound p.size +
            order.length * MeasuredPointAddition.depthBound p.size) := by
  change (Allocation.initializeWork p count).depth (fun _ => 1) path.1 +
    (placedConvertedCascade E points order coefficient).depth (fun _ => 1) path.2 ≤ _
  exact Nat.add_le_add (Allocation.initialize_depth p count (fun _ => 1) path.1)
    (placedConvertedCascade_depth (allowAllocation := true) E points order coefficient path.2)

/-- Actual initialization and converted execution reach only the same complete resident peak. -/
lemma convertedCircuit_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCircuit E points order coefficient).Path) :
    (convertedCircuit E points order coefficient).peakResidentSpace path =
      readySpace p.size count := by
  refine (Circuit.peakResidentSpace_seq (Allocation.initializeWork p count)
    (placedConvertedCascade E points order coefficient) path).trans ?_
  rw [Allocation.initialize_resident, placedConvertedCascade_resident (allowAllocation := true)]
  exact SpacePool.max_eq_right le_rfl

/-- Both preparations and every later call share the same exact fixed-role auxiliary peak. -/
lemma convertedCircuit_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (coefficient : (ZMod p)ˣ) (path : (convertedCircuit E points order coefficient).Path) :
    (convertedCircuit E points order coefficient).peakAuxiliarySpace path =
      readySpace p.size count := by
  refine (Circuit.peakAuxiliarySpace_seq (Allocation.initializeWork p count)
    (placedConvertedCascade E points order coefficient) path).trans ?_
  rw [Allocation.initialize_auxiliary, placedConvertedCascade_auxiliary (allowAllocation := true)]
  exact SpacePool.max_eq_right le_rfl

end

end MeasuredPlacement.Encoding
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
