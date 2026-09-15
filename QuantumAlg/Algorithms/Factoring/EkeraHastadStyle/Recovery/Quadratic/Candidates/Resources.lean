/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Operations
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sub.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Resources
import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Depth

/-!
# Independent native resources of actual quadratic candidates

The literal chain includes three initial native instructions, both real
saturating subtractions, the actual square root and the final addition.
For the actual work width `K`, every path uses at most `7 * K + 10` events
and unit-duration serial depth. Its independent coordinatewise allowance has
cardinality `7 * K + 12`, accounting for both possible subtraction labels.
The later two complete divisor checks are not part of this candidate budget.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open ClassicalRoutines.NumberTheory

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Independent native coordinates and multiplicities of every actual candidate instruction. -/
def nativeEnvelope (kind : ProblemKind) (width : Nat) : ResourcePool kind :=
  let work := RSA.quadraticWordWidth width
  ResourcePool.singleton (.classicalOperation (.wordResize width work)) +
    (ResourcePool.singleton (.classicalOperation (.wordUnary .increment work)) +
      (ResourcePool.singleton (.classicalOperation (.wordBinary .mulLow work)) +
        (NativeSub.nativeEnvelope kind work +
          (NativeSqrt.nativeEnvelope kind work +
            (NativeSub.nativeEnvelope kind work +
              ResourcePool.singleton (.classicalOperation (.wordBinary .add work)))))))

/-- Every actual candidate path fits the allowance in each complete native coordinate. -/
theorem nativeQuadratic_candidates_pool_le (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (path : (candidates input modulus refs).Path) :
    (candidates input modulus refs).resourcePool path ≤ nativeEnvelope kind width := by
  change ResourcePool.ofList
    ([.classicalOperation (.wordResize width (RSA.quadraticWordWidth width))] ++
      ([.classicalOperation (.wordUnary .increment (RSA.quadraticWordWidth width))] ++
        ([.classicalOperation (.wordBinary .mulLow (RSA.quadraticWordWidth width))] ++
          ((discriminant modulus refs).eventTrace path.2.2.2.1 ++
            ((squareRoot refs).eventTrace path.2.2.2.2.1 ++
              ((firstCandidate refs).eventTrace path.2.2.2.2.2.1 ++
                [.classicalOperation (.wordBinary .add (RSA.quadraticWordWidth width))])))))) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append,
    ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add le_rfl (add_le_add le_rfl (add_le_add le_rfl
    (add_le_add
      (NativeSub.nativeSub_into_pool_le (.storage refs.root.toCStorageRef) modulus refs.root
        path.2.2.2.1)
      (add_le_add
        (NativeSqrt.nativeSqrt_into_pool_le (.storage refs.root.toCStorageRef) refs.root
          path.2.2.2.2.1)
        (add_le_add
          (NativeSub.nativeSub_into_pool_le (.storage refs.center.toCStorageRef)
            (.storage refs.root.toCStorageRef) refs.first path.2.2.2.2.2.1) le_rfl)))))

/-- The complete independent coordinate allowance includes both labels of each subtraction. -/
theorem nativeQuadratic_nativeEnvelope_card (kind : ProblemKind) (width : Nat) :
    (nativeEnvelope kind width).card = 7 * RSA.quadraticWordWidth width + 12 := by
  simp [nativeEnvelope, NativeSub.nativeSub_nativeEnvelope_card,
    NativeSqrt.nativeSqrt_nativeEnvelope_card, ResourcePool.singleton]
  omega

/-- Actual event totals count only the selected label of each real subtraction branch. -/
theorem nativeQuadratic_candidates_eventCount_le (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (path : (candidates input modulus refs).Path) :
    ((candidates input modulus refs).resourcePool path).card ≤
      7 * RSA.quadraticWordWidth width + 10 := by
  change (ResourcePool.ofList
    ([.classicalOperation (.wordResize width (RSA.quadraticWordWidth width))] ++
      ([.classicalOperation (.wordUnary .increment (RSA.quadraticWordWidth width))] ++
        ([.classicalOperation (.wordBinary .mulLow (RSA.quadraticWordWidth width))] ++
          ((discriminant modulus refs).eventTrace path.2.2.2.1 ++
            ((squareRoot refs).eventTrace path.2.2.2.2.1 ++
              ((firstCandidate refs).eventTrace path.2.2.2.2.2.1 ++
                [.classicalOperation (.wordBinary .add
                  (RSA.quadraticWordWidth width))]))))))).card ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append,
    ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  simp only [Multiset.card_add]
  change 1 + (1 + (1 +
    (((discriminant modulus refs).resourcePool path.2.2.2.1).card +
      (((squareRoot refs).resourcePool path.2.2.2.2.1).card +
        (((firstCandidate refs).resourcePool path.2.2.2.2.2.1).card + 1))))) ≤ _
  have reduced : ((discriminant modulus refs).resourcePool path.2.2.2.1).card = 2 :=
    NativeSub.nativeSub_into_eventCount
      (.storage refs.root.toCStorageRef) modulus refs.root path.2.2.2.1
  have rooted : ((squareRoot refs).resourcePool path.2.2.2.2.1).card ≤
      7 * RSA.quadraticWordWidth width + 2 :=
    NativeSqrt.nativeSqrt_into_eventCount_le
      (.storage refs.root.toCStorageRef) refs.root path.2.2.2.2.1
  have lower : ((firstCandidate refs).resourcePool path.2.2.2.2.2.1).card = 2 :=
    NativeSub.nativeSub_into_eventCount (.storage refs.center.toCStorageRef)
      (.storage refs.root.toCStorageRef) refs.first path.2.2.2.2.2.1
  omega

/-- Unit-duration depth includes every actual sequential dependency in the candidate calculation. -/
theorem nativeQuadratic_candidates_unitDepth_le (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (refs : Refs ctx width) (path : (candidates input modulus refs).Path) :
    (candidates input modulus refs).depth (fun _ => 1) path ≤
      7 * RSA.quadraticWordWidth width + 10 := by
  change 1 + (1 + (1 +
    ((discriminant modulus refs).depth (fun _ => 1) path.2.2.2.1 +
      ((squareRoot refs).depth (fun _ => 1) path.2.2.2.2.1 +
        ((firstCandidate refs).depth (fun _ => 1) path.2.2.2.2.2.1 + 1))))) ≤ _
  have reduced : (discriminant modulus refs).depth (fun _ => 1) path.2.2.2.1 = 2 :=
    NativeSub.nativeSub_into_unitDepth
      (.storage refs.root.toCStorageRef) modulus refs.root path.2.2.2.1
  have rooted : (squareRoot refs).depth (fun _ => 1) path.2.2.2.2.1 ≤
      7 * RSA.quadraticWordWidth width + 2 :=
    NativeSqrt.nativeSqrt_into_unitDepth_le
      (.storage refs.root.toCStorageRef) refs.root path.2.2.2.2.1
  have lower : (firstCandidate refs).depth (fun _ => 1) path.2.2.2.2.2.1 = 2 :=
    NativeSub.nativeSub_into_unitDepth (.storage refs.center.toCStorageRef)
      (.storage refs.root.toCStorageRef) refs.first path.2.2.2.2.2.1
  omega

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
