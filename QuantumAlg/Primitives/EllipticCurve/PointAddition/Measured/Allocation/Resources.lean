/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Allocation
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Resources

/-!
# Charged initialization and actual placed point-addition resources

The actual initialization contributes both fixed quantum preparations, while
the retained cells contribute their real live storage. The placed body keeps
the accepted ordered events, evaluated depth and complete resident footprint.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation

noncomputable section

open Execution MeasuredUncompute

/-- Both concrete basis preparations are present in the literal initialization trace. -/
theorem initialize_eventTrace (modulus : Nat) (path : (initializeWork modulus).Path) :
    (initializeWork modulus).eventTrace path =
      [(InPlacePreparation.preparation modulus).event,
        (BasisPreparation.zero (selectorLayout modulus.size)).event] := by
  change [(InPlacePreparation.preparation modulus).event] ++
    ((allocateCells modulus.size).eventTrace path.2.1 ++
      [(BasisPreparation.zero (selectorLayout modulus.size)).event]) = _
  have noEvents : (allocateCells modulus.size).eventTrace path.2.1 = [] :=
    MeasurementCells.allocateFramed_eventTrace _ _ _ _ _ _
  rw [noEvents]
  rfl

/-- The two actual preparations retain their sequential duration dependency. -/
theorem initialize_depth (modulus : Nat) (duration : Resource.Event .quantum → Nat)
    (path : (initializeWork modulus).Path) :
    (initializeWork modulus).depth duration path =
      duration (InPlacePreparation.preparation modulus).event +
        duration (BasisPreparation.zero (selectorLayout modulus.size)).event := by
  change duration (InPlacePreparation.preparation modulus).event +
    ((allocateCells modulus.size).depth duration path.2.1 +
      duration (BasisPreparation.zero (selectorLayout modulus.size)).event) = _
  have noDepth : (allocateCells modulus.size).depth duration path.2.1 = 0 :=
    MeasurementCells.allocateFramed_depth _ _ _ _ _ _ _
  rw [noDepth, Nat.zero_add]

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

/-- Full execution includes initialization before the unchanged actual body trace. -/
theorem circuit_eventTrace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (circuit E Q).Path) :
    (circuit E Q).eventTrace path =
      [(InPlacePreparation.preparation p).event,
        (BasisPreparation.zero (selectorLayout p.size)).event] ++
          (placedBody E Q).eventTrace path.2 := by
  change (initializeWork p).eventTrace path.1 ++ (placedBody E Q).eventTrace path.2 = _
  rw [initialize_eventTrace]

/-- Independent native allowance includes both fixed preparations and the original body budget. -/
def eventBudget (modulus : Nat) : ResourcePool .quantum :=
  ResourcePool.ofList [(InPlacePreparation.preparation modulus).event,
    (BasisPreparation.zero (selectorLayout modulus.size)).event] + events modulus.size

/-- Every actual complete path charges preparation before the bounded native measured body. -/
theorem circuit_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (circuit E Q).Path) :
    (circuit E Q).resourcePool path ≤ eventBudget p := by
  have recorded := congrArg (ResourcePool.ofList (kind := .quantum))
    (circuit_eventTrace E Q path)
  exact recorded.le.trans ((ResourcePool.ofList_append _ _).le.trans
    (ResourcePool.add_mono le_rfl (placedBody_budget E Q path.2)))

/-- Two actual preparation steps precede the independently bounded measured execution depth. -/
theorem circuit_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (path : (circuit E Q).Path) :
    (circuit E Q).depth (fun _ => 1) path ≤ 2 + depthBound p.size := by
  change (initializeWork p).depth (fun _ => 1) path.1 +
    (placedBody E Q).depth (fun _ => 1) path.2 ≤ _
  rw [initialize_depth]
  exact Nat.add_le_add_left (placedBody_depth E Q path.2) 2

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition.Allocation
