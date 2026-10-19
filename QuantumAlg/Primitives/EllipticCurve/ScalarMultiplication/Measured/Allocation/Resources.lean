/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Resources
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# Charged initialization and native measured cascade resources

The actual prefix charges every zero preparation and fixed X load. The
original finite result cells are retained there and used by the following
measured cascade. Native events and serial depth include the prefix and every
actual point call in the supplied order.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution MeasuredUncompute

/-- The literal initialization trace includes every zero preparation and fixed X load. -/
lemma initialize_eventTrace (modulus count : Nat) (path : (initializeWork modulus count).Path) :
    (initializeWork modulus count).eventTrace path = initializationTrace modulus count :=
  initializeWork_eventTrace modulus count path

/-- The real preparation and loading dependencies fit their exact event allowance. -/
lemma initialize_depth (modulus count : Nat)
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (path : (initializeWork modulus count).Path) :
    (initializeWork modulus count).depth duration path ≤
      ResourcePool.weightedCount duration
        (ResourcePool.ofList (initializationTrace modulus count)) := by
  exact (Circuit.depth_le_weightedCount_of_pool_le _ duration _ path
    (initializeWork_resourcePool modulus count path).le)

/-- The complete original cascade outcomes identify all actual post-allocation execution paths. -/
def placedPathEquiv {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (allowAllocation : Bool := true) :
    (cascade E points order false).Path ≃ (placedCascade E points order allowAllocation).Path :=
  Equiv.refl _

/-- The post-allocation code emits the same complete ordered native cascade events. -/
lemma placedCascade_eventTrace {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order false).Path) :
    (placedCascade E points order allowAllocation).eventTrace
        (placedPathEquiv E points order allowAllocation path) =
      (cascade E points order false).eventTrace path := rfl

/-- Placement preserves the independent per-invocation native event bound. -/
lemma placedCascade_budget {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (placedCascade E points order allowAllocation).Path) :
    (placedCascade E points order allowAllocation).resourcePool path ≤
      ResourcePool.scale order.length (MeasuredPointAddition.events p.size) := by
  exact (Circuit.resourcePool_embed (allowAllocation := allowAllocation)
    (ContextEmbedding.alongPermutation (body_entries p.size count))
    (cascade E points order false) path).le.trans
      (cascade_budget (allowAllocation := false) E points order path)

/-- The actual post-allocation cascade retains its independent serial native depth bound. -/
lemma placedCascade_depth {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (placedCascade E points order allowAllocation).Path) :
    (placedCascade E points order allowAllocation).depth (fun _ => 1) path ≤
      order.length * MeasuredPointAddition.depthBound p.size := by
  exact cascade_depth (allowAllocation := false) E points order path

/-- The allocated cascade keeps the exact complete common resident capacity. -/
lemma placedCascade_resident {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (placedCascade E points order allowAllocation).Path) :
    (placedCascade E points order allowAllocation).peakResidentSpace path =
      readySpace p.size count :=
  (Circuit.peakResidentSpace_embed (allowAllocation := allowAllocation)
    (ContextEmbedding.alongPermutation (body_entries p.size count))
    (cascade E points order false) path).trans
      ((ContextPermutation.resident_space (body_entries p.size count)).symm.trans
        (readyContext_resident_exact p.size count))

/-- The same complete entries retain their original auxiliary roles after allocation placement. -/
lemma placedCascade_auxiliary {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (placedCascade E points order allowAllocation).Path) :
    (placedCascade E points order allowAllocation).peakAuxiliarySpace path =
      readySpace p.size count :=
  (Circuit.peakAuxiliarySpace_embed (allowAllocation := allowAllocation)
    (ContextEmbedding.alongPermutation (body_entries p.size count))
    (cascade E points order false) path).trans
      ((ContextPermutation.auxiliary_space (body_entries p.size count)).symm.trans
        (readyContext_auxiliary_exact p.size count))

/-- Input-determined preparation allowance and every prescribed point call. -/
def eventBudget (modulus count calls : Nat) :
    ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ResourcePool.ofList (initializationTrace modulus count) +
      ResourcePool.scale calls (MeasuredPointAddition.events modulus.size)

/-- Every actual complete path charges initialization and all following measured point calls. -/
lemma circuit_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (circuit E points order).Path) :
    (circuit E points order).resourcePool path ≤ eventBudget p count order.length := by
  change ResourcePool.ofList ((initializeWork p count).eventTrace path.1 ++
    (placedCascade E points order).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, initialize_eventTrace]
  exact ResourcePool.add_mono le_rfl
    (placedCascade_budget (allowAllocation := true) E points order path.2)

/-- Every preparation and X load precedes the complete cascade duration. -/
lemma circuit_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (circuit E points order).Path) :
    (circuit E points order).depth (fun _ => 1) path ≤
      ResourcePool.weightedCount (fun _ => 1)
        (ResourcePool.ofList (initializationTrace p count)) +
          order.length * MeasuredPointAddition.depthBound p.size := by
  change (initializeWork p count).depth (fun _ => 1) path.1 +
    (placedCascade E points order).depth (fun _ => 1) path.2 ≤ _
  exact Nat.add_le_add (initialize_depth p count (fun _ => 1) path.1)
    (placedCascade_depth (allowAllocation := true) E points order path.2)

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
