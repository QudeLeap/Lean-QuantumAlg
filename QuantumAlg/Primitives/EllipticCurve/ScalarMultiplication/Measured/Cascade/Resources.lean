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
lemma cascade_budget {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order allowAllocation).Path) :
    (cascade E points order allowAllocation).resourcePool path ≤
      ResourcePool.scale order.length (MeasuredPointAddition.events p.size) := by
  induction order with
  | nil => exact le_rfl
  | cons active remaining ih =>
      change ResourcePool.ofList
        ((step E (points active) active allowAllocation).eventTrace path.1 ++
        (cascade E points remaining allowAllocation).eventTrace path.2) ≤ _
      rw [ResourcePool.ofList_append, List.length_cons, ResourcePool.scale_succ]
      exact add_le_add
        (step_budget (allowAllocation := allowAllocation) E (points active) active path.1)
        (ih path.2)

/-- Actual serial native depth adds the independent point allowance for each prescribed call. -/
lemma cascade_depth {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order allowAllocation).Path) :
    (cascade E points order allowAllocation).depth (fun _ => 1) path ≤
      order.length * MeasuredPointAddition.depthBound p.size := by
  induction order with
  | nil => exact Nat.zero_le _
  | cons active remaining ih =>
      change (step E (points active) active allowAllocation).depth (fun _ => 1) path.1 +
        (cascade E points remaining allowAllocation).depth (fun _ => 1) path.2 ≤ _
      simpa only [List.length_cons, Nat.succ_mul, Nat.add_comm] using
        Nat.add_le_add
          (step_depth (allowAllocation := allowAllocation) E (points active) active path.1)
          (ih path.2)

/-- Every visited live context is the same complete measured workspace and all exponent systems. -/
lemma cascade_visited {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order allowAllocation).Path) (visited : RuntimeCtx .quantum)
    (present : visited ∈ (cascade E points order allowAllocation).visitedContexts path) :
    visited = readyContext p.size count := by
  induction order with
  | nil =>
      change visited ∈ [readyContext p.size count] at present
      exact List.mem_singleton.mp present
  | cons active remaining ih =>
      change visited ∈ (step E (points active) active allowAllocation).visitedContexts path.1 ++
        (cascade E points remaining allowAllocation).visitedContexts path.2 at present
      rcases List.mem_append.mp present with first | rest
      · simpa only [step_visited, List.mem_singleton] using first
      · exact ih path.2 rest

private lemma cascade_pre_mem {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order allowAllocation).Path) :
    readyContext p.size count ∈ (cascade E points order allowAllocation).visitedContexts path := by
  cases order with
  | nil => exact List.mem_singleton_self _
  | cons active remaining =>
      change readyContext p.size count ∈
        (step E (points active) active allowAllocation).visitedContexts path.1 ++
        (cascade E points remaining allowAllocation).visitedContexts path.2
      apply List.mem_append_left
      rw [step_visited]
      exact List.mem_singleton_self _

/-- The exact resident peak is one shared complete workspace, including for an empty cascade. -/
lemma cascade_resident {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order allowAllocation).Path) :
    (cascade E points order allowAllocation).peakResidentSpace path = readySpace p.size count := by
  have upper := (cascade E points order allowAllocation).peakResidentSpace_le_of_visited path
    (readySpace p.size count) (by
      intro visited present
      rw [cascade_visited (allowAllocation := allowAllocation) E points order path visited present,
        readyContext_resident_exact])
  have lower := (cascade E points order allowAllocation).residentSpace_le_peak_of_visited path
    (readyContext p.size count)
    (cascade_pre_mem (allowAllocation := allowAllocation) E points order path)
  rw [readyContext_resident_exact] at lower
  exact le_antisymm upper lower

/-- Fixed ownership roles give the same complete auxiliary peak across all actual calls. -/
lemma cascade_auxiliary {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (order : List (Fin count))
    (path : (cascade E points order allowAllocation).Path) :
    (cascade E points order allowAllocation).peakAuxiliarySpace path = readySpace p.size count := by
  have upper := (cascade E points order allowAllocation).peakAuxiliarySpace_le_of_visited path
    (readySpace p.size count) (by
      intro visited present
      rw [cascade_visited (allowAllocation := allowAllocation) E points order path visited present,
        readyContext_auxiliary_exact])
  have lower := (cascade E points order allowAllocation).auxiliarySpace_le_peak_of_visited path
    (readyContext p.size count)
    (cascade_pre_mem (allowAllocation := allowAllocation) E points order path)
  rw [readyContext_auxiliary_exact] at lower
  exact le_antisymm upper lower

/-- Increasing-index execution charges exactly count copies of the independent point allowance. -/
lemma fullCascade_budget {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E)
    (path : (fullCascade E points allowAllocation).Path) :
    (fullCascade E points allowAllocation).resourcePool path ≤
      ResourcePool.scale count (MeasuredPointAddition.events p.size) := by
  simpa only [fullCascade, List.length_finRange] using
    cascade_budget (allowAllocation := allowAllocation) E points (List.finRange count) path

/-- The full increasing-index cascade has the independent count-times-point serial depth bound. -/
lemma fullCascade_depth {allowAllocation : Bool} {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E)
    (path : (fullCascade E points allowAllocation).Path) :
    (fullCascade E points allowAllocation).depth (fun _ => 1) path ≤
      count * MeasuredPointAddition.depthBound p.size := by
  simpa only [fullCascade, List.length_finRange] using
    cascade_depth (allowAllocation := allowAllocation) E points (List.finRange count) path

end

end MeasuredPlacement
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ScalarMultiplication
