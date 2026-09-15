/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Allocation
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing.Resources

/-!
# Charged initialization and native measured cascade resources

Both fixed quantum preparations occur in the actual prefix. The original
finite result cells are retained there and used by the following measured
cascade. Native events and serial depth include the prefix and every actual
point call in the supplied order.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement.Allocation

noncomputable section

open Execution MeasuredUncompute

/-- The two concrete preparations both occur in the actual initialization trace. -/
theorem initialize_eventTrace (modulus count : Nat) (path : (initializeWork modulus count).Path) :
    (initializeWork modulus count).eventTrace path =
      [(InPlacePreparation.preparation modulus).event,
        (BasisPreparation.zero (indexedLayout modulus.size count)).event] := by
  change [(InPlacePreparation.preparation modulus).event] ++
    ((allocateCells modulus.size count).eventTrace path.2.1 ++
      [(BasisPreparation.zero (indexedLayout modulus.size count)).event]) = _
  have noEvents : (allocateCells modulus.size count).eventTrace path.2.1 = [] :=
    MeasurementCells.allocateFramed_eventTrace _ _ _ _ _ _
  rw [noEvents]
  rfl

/-- Actual initialization has the chronological duration of its two charged preparations. -/
theorem initialize_depth (modulus count : Nat) (duration : Resource.Event .quantum → Nat)
    (path : (initializeWork modulus count).Path) :
    (initializeWork modulus count).depth duration path =
      duration (InPlacePreparation.preparation modulus).event +
        duration (BasisPreparation.zero (indexedLayout modulus.size count)).event := by
  change duration (InPlacePreparation.preparation modulus).event +
    ((allocateCells modulus.size count).depth duration path.2.1 +
      duration (BasisPreparation.zero (indexedLayout modulus.size count)).event) = _
  have noDepth : (allocateCells modulus.size count).depth duration path.2.1 = 0 :=
    MeasurementCells.allocateFramed_depth _ _ _ _ _ _ _
  rw [noDepth, Nat.zero_add]

/-- The complete original cascade outcomes identify all actual post-allocation execution paths. -/
def placedPathEquiv {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count)) :
    (cascade E points order).Path ≃ (placedCascade E points order).Path :=
  ContextPermutation.localPathEquiv (cascade E points order) (cascade_isLocal E points order)
    (after p.size count) (body_entries p.size count)

/-- The post-allocation code emits the same complete ordered native cascade events. -/
theorem placedCascade_eventTrace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order).Path) :
    (placedCascade E points order).eventTrace (placedPathEquiv E points order path) =
      (cascade E points order).eventTrace path :=
  ContextPermutation.localCircuit_eventTrace _ _ _ _ path

/-- Placement preserves the independent per-invocation native event bound. -/
theorem placedCascade_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (placedCascade E points order).Path) :
    (placedCascade E points order).resourcePool path ≤
      ResourcePool.scale order.length (MeasuredPointAddition.events p.size) := by
  obtain ⟨original, rfl⟩ := (placedPathEquiv E points order).surjective path
  exact (ContextPermutation.localCircuit_resourcePool _ _ _ _ original).le.trans
    (cascade_budget E points order original)

/-- The actual post-allocation cascade retains its independent serial native depth bound. -/
theorem placedCascade_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (placedCascade E points order).Path) :
    (placedCascade E points order).depth (fun _ => 1) path ≤
      order.length * MeasuredPointAddition.depthBound p.size := by
  obtain ⟨original, rfl⟩ := (placedPathEquiv E points order).surjective path
  exact (ContextPermutation.localCircuit_depth _ _ _ _ (fun _ => 1) original).le.trans
    (cascade_depth E points order original)

/-- The allocated cascade keeps the exact complete common resident capacity. -/
theorem placedCascade_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (placedCascade E points order).Path) :
    (placedCascade E points order).peakResidentSpace path = readySpace p.size count :=
  (ContextPermutation.localCircuit_peakResidentSpace _ _ _ path).trans
    (readyContext_resident_exact p.size count)

/-- The same complete entries retain their original auxiliary roles after allocation placement. -/
theorem placedCascade_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (placedCascade E points order).Path) :
    (placedCascade E points order).peakAuxiliarySpace path = readySpace p.size count :=
  (ContextPermutation.localCircuit_peakAuxiliarySpace _ _ _ path).trans
    (readyContext_auxiliary_exact p.size count)

/-- Independent native allowance includes both preparations and every prescribed point call. -/
def eventBudget (modulus count calls : Nat) : ResourcePool .quantum :=
  ResourcePool.ofList [(InPlacePreparation.preparation modulus).event,
    (BasisPreparation.zero (indexedLayout modulus.size count)).event] +
      ResourcePool.scale calls (MeasuredPointAddition.events modulus.size)

/-- Every actual complete path charges initialization and all following measured point calls. -/
theorem circuit_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (circuit E points order).Path) :
    (circuit E points order).resourcePool path ≤ eventBudget p count order.length := by
  change ResourcePool.ofList ((initializeWork p count).eventTrace path.1 ++
    (placedCascade E points order).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, initialize_eventTrace]
  exact ResourcePool.add_mono le_rfl (placedCascade_budget E points order path.2)

/-- Two preparations precede the independent complete cascade serial depth allowance. -/
theorem circuit_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (circuit E points order).Path) :
    (circuit E points order).depth (fun _ => 1) path ≤
      2 + order.length * MeasuredPointAddition.depthBound p.size := by
  change (initializeWork p count).depth (fun _ => 1) path.1 +
    (placedCascade E points order).depth (fun _ => 1) path.2 ≤ _
  rw [initialize_depth]
  exact Nat.add_le_add_left (placedCascade_depth E points order path.2) 2

end

end MeasuredPlacement.Allocation
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
