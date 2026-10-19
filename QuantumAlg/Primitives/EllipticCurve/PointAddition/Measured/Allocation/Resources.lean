/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Resources
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Execution.Composition.Resources

/-!
# Charged initialization and actual placed point-addition resources

The actual initialization charges every zero preparation and fixed X load;
retained cells contribute their live storage. The placed body keeps the
accepted ordered events, depth and complete resident footprint.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

open Execution MeasuredUncompute

/-- The literal initialization trace contains every zero preparation and fixed X load. -/
lemma initialize_eventTrace (modulus : Nat) (path : (initializeWork modulus).Path) :
    (initializeWork modulus).eventTrace path = initializationTrace modulus :=
  initializeWork_eventTrace modulus path

/-- The real preparation and load dependencies fit their exact event allowance. -/
lemma initialize_depth (modulus : Nat)
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (path : (initializeWork modulus).Path) :
    (initializeWork modulus).depth duration path ≤
      ResourcePool.weightedCount duration (ResourcePool.ofList (initializationTrace modulus)) := by
  exact (Circuit.depth_le_weightedCount_of_pool_le _ duration _ path
    (initializeWork_resourcePool modulus path).le)

/-- Every path of the placed body corresponds to an original actual body path. -/
def placedPathEquiv {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : (body E Q).Path ≃ (placedBody E Q).Path :=
  Equiv.refl _

/-- The same ordered native events are emitted on corresponding actual paths. -/
lemma placedBody_eventTrace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (body E Q).Path) :
    (placedBody E Q).eventTrace (placedPathEquiv E Q path) = (body E Q).eventTrace path := rfl

/-- The actual body retains its independent native event budget after allocation placement. -/
lemma placedBody_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (placedBody E Q).Path) :
    (placedBody E Q).resourcePool path ≤ events p.size := by
  exact (Circuit.resourcePool_embed (allowAllocation := true)
    (ContextEmbedding.alongPermutation (body_entries p.size))
    (body E Q false) path).le.trans (body_budget E Q (allowAllocation := false) path)

/-- The same evaluated serial duration bound holds on every actual placed path. -/
lemma placedBody_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (placedBody E Q).Path) :
    (placedBody E Q).depth (fun _ => 1) path ≤ depthBound p.size := by
  exact body_depth E Q (allowAllocation := false) path

/-- Every original live cell and native-dimensional system remains resident in the placed body. -/
lemma placedBody_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (placedBody E Q).Path) :
    (placedBody E Q).peakResidentSpace path = space p.size :=
  (Circuit.peakResidentSpace_embed (allowAllocation := true)
    (ContextEmbedding.alongPermutation (body_entries p.size))
    (body E Q false) path).trans
      ((ContextPermutation.resident_space (body_entries p.size)).symm.trans
        (context_resident p.size))

/-- Unchanged actual storage roles give the same auxiliary capacity of the placed body. -/
lemma placedBody_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (placedBody E Q).Path) :
    (placedBody E Q).peakAuxiliarySpace path = space p.size :=
  (Circuit.peakAuxiliarySpace_embed (allowAllocation := true)
    (ContextEmbedding.alongPermutation (body_entries p.size))
    (body E Q false) path).trans
      ((ContextPermutation.auxiliary_space (body_entries p.size)).symm.trans
        (context_auxiliary p.size))

/-- Full execution includes every initialization event before the unchanged body trace. -/
lemma circuit_eventTrace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (circuit E Q).Path) :
    (circuit E Q).eventTrace path =
      initializationTrace p ++ (placedBody E Q).eventTrace path.2 := by
  change (initializeWork p).eventTrace path.1 ++ (placedBody E Q).eventTrace path.2 = _
  rw [initialize_eventTrace]

/-- The input-determined preparation allowance and native body allowance. -/
def eventBudget (modulus : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ResourcePool.ofList (initializationTrace modulus) + events modulus.size

/-- Every actual complete path charges preparation before the bounded native measured body. -/
lemma circuit_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (circuit E Q).Path) :
    (circuit E Q).resourcePool path ≤ eventBudget p := by
  have recorded := congrArg (ResourcePool.ofList (model := .quantum AlgorithmGate.model .empty))
    (circuit_eventTrace E Q path)
  exact recorded.le.trans ((ResourcePool.ofList_append _ _).le.trans
    (ResourcePool.add_mono le_rfl (placedBody_budget E Q path.2)))

/-- Every preparation and X load precedes the independently bounded measured body. -/
lemma circuit_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (circuit E Q).Path) :
    (circuit E Q).depth (fun _ => 1) path ≤
      ResourcePool.weightedCount (fun _ => 1)
        (ResourcePool.ofList (initializationTrace p)) + depthBound p.size := by
  change (initializeWork p).depth (fun _ => 1) path.1 +
    (placedBody E Q).depth (fun _ => 1) path.2 ≤ _
  exact Nat.add_le_add (initialize_depth p (fun _ => 1) path.1)
    (placedBody_depth E Q path.2)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation
