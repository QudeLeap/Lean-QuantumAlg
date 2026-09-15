/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Step.Resources

/-!
# Native resources of the actual measured scalar cascade

The independent point allowance adds once per actual list item. The full
common workspace remains resident throughout every call, so its peak does
not scale with the number of invocations. Even the empty cascade retains
its complete actual input context.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
namespace MeasuredPlacement

noncomputable section

open Execution

/-- Every actually executed point call is charged by the original independent point allowance. -/
theorem cascade_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order).Path) :
    (cascade E points order).resourcePool path ≤
      ResourcePool.scale order.length (MeasuredPointAddition.events p.size) := by
  induction order with
  | nil => exact le_rfl
  | cons active remaining ih =>
      change ResourcePool.ofList ((step E (points active) active).eventTrace path.1 ++
        (cascade E points remaining).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append, List.length_cons, ResourcePool.scale_succ]
      exact add_le_add (step_budget E (points active) active path.1) (ih path.2)

/-- Actual serial native depth adds the independent point allowance for each prescribed call. -/
theorem cascade_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order).Path) :
    (cascade E points order).depth (fun _ => 1) path ≤
      order.length * MeasuredPointAddition.depthBound p.size := by
  induction order with
  | nil => exact Nat.zero_le _
  | cons active remaining ih =>
      change (step E (points active) active).depth (fun _ => 1) path.1 +
        (cascade E points remaining).depth (fun _ => 1) path.2 ≤ _
      simpa only [List.length_cons, Nat.succ_mul, Nat.add_comm] using
        Nat.add_le_add (step_depth E (points active) active path.1) (ih path.2)

/-- Every visited live context is the same complete measured workspace and all exponent systems. -/
theorem cascade_visited {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order).Path) (visited : RuntimeCtx .quantum)
    (present : visited ∈ (cascade E points order).visitedContexts path) :
    visited = readyContext p.size count :=
  ContextUnion.local_visited _ (cascade_isLocal E points order) path visited present

/-- The exact resident peak is one shared complete workspace, including for an empty cascade. -/
theorem cascade_resident {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order).Path) :
    (cascade E points order).peakResidentSpace path = readySpace p.size count := by
  have upper := (cascade E points order).peakResidentSpace_le_of_visited path
    (readySpace p.size count) (by
      intro visited present
      rw [cascade_visited E points order path visited present, readyContext_resident_exact])
  have lower := (cascade E points order).residentSpace_le_peak_of_visited path
    (readyContext p.size count)
    (ContextUnion.local_pre_mem _ (cascade_isLocal E points order) path)
  rw [readyContext_resident_exact] at lower
  exact le_antisymm upper lower

/-- Fixed ownership roles give the same complete auxiliary peak across all actual calls. -/
theorem cascade_auxiliary {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order).Path) :
    (cascade E points order).peakAuxiliarySpace path = readySpace p.size count := by
  have upper := (cascade E points order).peakAuxiliarySpace_le_of_visited path
    (readySpace p.size count) (by
      intro visited present
      rw [cascade_visited E points order path visited present, readyContext_auxiliary_exact])
  have lower := (cascade E points order).auxiliarySpace_le_peak_of_visited path
    (readyContext p.size count)
    (ContextUnion.local_pre_mem _ (cascade_isLocal E points order) path)
  rw [readyContext_auxiliary_exact] at lower
  exact le_antisymm upper lower

/-- Increasing-index execution charges exactly count copies of the independent point allowance. -/
theorem fullCascade_budget {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (path : (fullCascade E points).Path) :
    (fullCascade E points).resourcePool path ≤
      ResourcePool.scale count (MeasuredPointAddition.events p.size) := by
  simpa only [fullCascade, List.length_finRange] using
    cascade_budget E points (List.finRange count) path

/-- The full increasing-index cascade has the independent count-times-point serial depth bound. -/
theorem fullCascade_depth {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (path : (fullCascade E points).Path) :
    (fullCascade E points).depth (fun _ => 1) path ≤
      count * MeasuredPointAddition.depthBound p.size := by
  simpa only [fullCascade, List.length_finRange] using
    cascade_depth E points (List.finRange count) path

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
