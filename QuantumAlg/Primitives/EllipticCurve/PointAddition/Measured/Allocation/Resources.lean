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
theorem initialize_eventTrace (modulus : Nat) (path : (initializeWork modulus).Path) :
    (initializeWork modulus).eventTrace path = initializationTrace modulus :=
  initializeWork_eventTrace modulus path

/-- The real preparation and load dependencies fit their exact event allowance. -/
theorem initialize_depth (modulus : Nat)
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (path : (initializeWork modulus).Path) :
    (initializeWork modulus).depth duration path ≤
      ResourcePool.weightedCount duration (ResourcePool.ofList (initializationTrace modulus)) := by
  exact (Circuit.depth_le_weightedCount_of_pool_le _ duration _ path
    (initializeWork_resourcePool modulus path).le)

/-- Every path of the placed body corresponds to an original actual body path. -/
def placedPathEquiv {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) : (body E Q).Path ≃ (placedBody E Q).Path :=
  ContextPermutation.localPathEquiv (body E Q) (body_isLocal E Q) (after p.size)
    (body_entries p.size)

/-- The same ordered native events are emitted on corresponding actual paths. -/
theorem placedBody_eventTrace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (body E Q).Path) :
    (placedBody E Q).eventTrace (placedPathEquiv E Q path) = (body E Q).eventTrace path :=
  ContextPermutation.localCircuit_eventTrace _ _ _ _ path

/-- The actual body retains its independent native event budget after allocation placement. -/
theorem placedBody_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (placedBody E Q).Path) :
    (placedBody E Q).resourcePool path ≤ events p.size := by
  obtain ⟨original, rfl⟩ := (placedPathEquiv E Q).surjective path
  exact (ContextPermutation.localCircuit_resourcePool _ _ _ _ original).le.trans
    (body_budget E Q original)

/-- The same evaluated serial duration bound holds on every actual placed path. -/
theorem placedBody_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (placedBody E Q).Path) :
    (placedBody E Q).depth (fun _ => 1) path ≤ depthBound p.size := by
  obtain ⟨original, rfl⟩ := (placedPathEquiv E Q).surjective path
  exact (ContextPermutation.localCircuit_depth _ _ _ _ (fun _ => 1) original).le.trans
    (body_depth E Q original)

/-- Every original live cell and native-dimensional system remains resident in the placed body. -/
theorem placedBody_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (placedBody E Q).Path) :
    (placedBody E Q).peakResidentSpace path = space p.size :=
  (ContextPermutation.localCircuit_peakResidentSpace _ _ _ path).trans (context_resident p.size)

/-- Unchanged actual storage roles give the same auxiliary capacity of the placed body. -/
theorem placedBody_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (placedBody E Q).Path) :
    (placedBody E Q).peakAuxiliarySpace path = space p.size :=
  (ContextPermutation.localCircuit_peakAuxiliarySpace _ _ _ path).trans (context_auxiliary p.size)

/-- Full execution includes every initialization event before the unchanged body trace. -/
theorem circuit_eventTrace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (circuit E Q).Path) :
    (circuit E Q).eventTrace path =
      initializationTrace p ++ (placedBody E Q).eventTrace path.2 := by
  change (initializeWork p).eventTrace path.1 ++ (placedBody E Q).eventTrace path.2 = _
  rw [initialize_eventTrace]

/-- The input-determined preparation allowance and native body allowance. -/
def eventBudget (modulus : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  ResourcePool.ofList (initializationTrace modulus) + events modulus.size

/-- Every actual complete path charges preparation before the bounded native measured body. -/
theorem circuit_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (circuit E Q).Path) :
    (circuit E Q).resourcePool path ≤ eventBudget p := by
  have recorded := congrArg (ResourcePool.ofList (model := .quantum AlgorithmGate.model .empty))
    (circuit_eventTrace E Q path)
  exact recorded.le.trans ((ResourcePool.ofList_append _ _).le.trans
    (ResourcePool.add_mono le_rfl (placedBody_budget E Q path.2)))

/-- Every preparation and X load precedes the independently bounded measured body. -/
theorem circuit_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
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
