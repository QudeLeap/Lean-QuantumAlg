/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Pair.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection.Narrow.Resources

/-!
# Actual native resources of complete scoped quadratic recovery

With K = 2 * (width + 1), the independent native allowance contains 7*K+39
entries. Every actual path, including both complete divisor checks and the
final persistent selector, has at most 7*K+37 events and the same bound on
unit-duration serial depth. The different totals retain both possible labels
of each subtraction in the coordinate budget while counting only the label
actually executed on a path. All real initialization and resize events count.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width resultWidth : Nat}

/-- The two actual initialization labels load one after the candidates have been materialized. -/
def programOneEvents (kind : ProblemKind) (width : Nat) : List (Resource.Event kind) :=
  [.classicalOperation (.wordBinary .bitXor (RSA.quadraticWordWidth width)),
    .classicalOperation (.wordUnary .increment (RSA.quadraticWordWidth width))]

/-- Independent native coordinate allowance for the complete actual scoped program. -/
def programNativeEnvelope (kind : ProblemKind) (width resultWidth : Nat) : ResourcePool kind :=
  (nativeEnvelope kind width + ResourcePool.ofList (programOneEvents kind width)) +
    (Pair.nativeEnvelope kind (RSA.quadraticWordWidth width) +
      NarrowSelection.nativeEnvelope kind (RSA.quadraticWordWidth width) resultWidth)

/-- All actual scopes retain exactly the chronological traces of the four executed blocks. -/
theorem nativeQuadratic_program_eventTrace (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (path : (program input modulus original).Path) :
    (program input modulus original).eventTrace path =
      ((candidates (LocalLayout.arithmeticRead input width)
        (LocalLayout.arithmeticRead modulus width)
        (LocalLayout.arithmeticRefs ctx width)).eventTrace path.1.1 ++
          programOneEvents kind width) ++
      ((Pair.code (LocalLayout.pairRefs modulus)).eventTrace path.2.1 ++
        (NarrowSelection.code
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
          (LocalLayout.persistentRefs original width)).eventTrace path.2.2) := rfl

private theorem pool_groups (first second third fourth : List (Resource.Event kind)) :
    ResourcePool.ofList ((first ++ second) ++ (third ++ fourth)) =
      (ResourcePool.ofList first + ResourcePool.ofList second) +
        (ResourcePool.ofList third + ResourcePool.ofList fourth) := by
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]

/-- The actual program ledger is precisely the sum of its four actual block ledgers. -/
theorem nativeQuadratic_program_resourcePool (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (path : (program input modulus original).Path) :
    (program input modulus original).resourcePool path =
      ((candidates (LocalLayout.arithmeticRead input width)
        (LocalLayout.arithmeticRead modulus width)
        (LocalLayout.arithmeticRefs ctx width)).resourcePool path.1.1 +
          ResourcePool.ofList (programOneEvents kind width)) +
      ((Pair.code (LocalLayout.pairRefs modulus)).resourcePool path.2.1 +
        (NarrowSelection.code
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
          (LocalLayout.persistentRefs original width)).resourcePool path.2.2) :=
  (congrArg ResourcePool.ofList
    (nativeQuadratic_program_eventTrace input modulus original path)).trans
    (pool_groups _ _ _ _)

/-- Every actual event coordinate is dominated by the independent complete-program allowance. -/
theorem nativeQuadratic_program_pool_le (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (path : (program input modulus original).Path) :
    (program input modulus original).resourcePool path ≤
      programNativeEnvelope kind width resultWidth := by
  have actual := nativeQuadratic_program_resourcePool input modulus original path
  refine actual.le.trans ?_
  exact add_le_add
    (add_le_add (nativeQuadratic_candidates_pool_le (LocalLayout.arithmeticRead input width)
      (LocalLayout.arithmeticRead modulus width) (LocalLayout.arithmeticRefs ctx width)
      path.1.1) le_rfl)
    (add_le_add (Pair.nativeQuadratic_pair_pool_le (LocalLayout.pairRefs modulus) path.2.1)
      (NarrowSelection.nativeQuadratic_narrow_pool_le
        (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
        (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
        (LocalLayout.persistentRefs original width) path.2.2))

/-- The independent pool includes both subtraction labels and every possible copy instruction. -/
theorem nativeQuadratic_program_nativeEnvelope_card (kind : ProblemKind)
    (width resultWidth : Nat) :
    (programNativeEnvelope kind width resultWidth).card =
      7 * RSA.quadraticWordWidth width + 39 := by
  rw [programNativeEnvelope, Multiset.card_add, Multiset.card_add, Multiset.card_add,
    nativeQuadratic_nativeEnvelope_card, Pair.nativeQuadratic_pair_nativeEnvelope_card,
    NarrowSelection.nativeQuadratic_narrow_nativeEnvelope_card]
  have oneCount : (ResourcePool.ofList (programOneEvents kind width)).card = 2 := rfl
  rw [oneCount]

private theorem count_groups (first second third fourth : ResourcePool kind) :
    ((first + second) + (third + fourth)).card =
      (first.card + second.card) + (third.card + fourth.card) := by
  simp only [Multiset.card_add]

private theorem narrow_total_le (taken : Bool) : (if taken then 5 else 3) ≤ 5 := by
  cases taken <;> decide

/-- The actual event total counts only the subtraction and selector arms actually executed. -/
theorem nativeQuadratic_program_eventCount_le (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (path : (program input modulus original).Path) :
    ((program input modulus original).resourcePool path).card ≤
      7 * RSA.quadraticWordWidth width + 37 := by
  have count := (congrArg (fun pool : ResourcePool kind => pool.card)
    (nativeQuadratic_program_resourcePool input modulus original path)).trans
      (count_groups _ _ _ _)
  have candidatesBound := nativeQuadratic_candidates_eventCount_le
    (LocalLayout.arithmeticRead input width) (LocalLayout.arithmeticRead modulus width)
    (LocalLayout.arithmeticRefs ctx width) path.1.1
  have pairBound := (Pair.nativeQuadratic_pair_total_le
    (LocalLayout.pairRefs modulus) path.2.1).1
  have narrowCount := NarrowSelection.nativeQuadratic_narrow_eventCount
    (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
    (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
    (LocalLayout.persistentRefs original width) path.2.2
  have narrowBound := (narrowCount.le.trans (narrow_total_le _))
  have oneCount : (ResourcePool.ofList (programOneEvents kind width)).card = 2 := rfl
  omega

/-- Unit-duration depth follows the identical actual serial block order through every scope. -/
theorem nativeQuadratic_program_unitDepth_le (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (path : (program input modulus original).Path) :
    (program input modulus original).depth (fun _ => 1) path ≤
      7 * RSA.quadraticWordWidth width + 37 := by
  have count : (program input modulus original).depth (fun _ => 1) path =
      ((candidates (LocalLayout.arithmeticRead input width)
        (LocalLayout.arithmeticRead modulus width) (LocalLayout.arithmeticRefs ctx width)).depth
          (fun _ => 1) path.1.1 + 2) +
      ((Pair.code (LocalLayout.pairRefs modulus)).depth (fun _ => 1) path.2.1 +
        (NarrowSelection.code
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
          (LocalLayout.persistentRefs original width)).depth (fun _ => 1) path.2.2) := rfl
  have candidatesBound := nativeQuadratic_candidates_unitDepth_le
    (LocalLayout.arithmeticRead input width) (LocalLayout.arithmeticRead modulus width)
    (LocalLayout.arithmeticRefs ctx width) path.1.1
  have pairBound := (Pair.nativeQuadratic_pair_total_le
    (LocalLayout.pairRefs modulus) path.2.1).2
  have narrowCount := NarrowSelection.nativeQuadratic_narrow_unitDepth
    (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
    (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
    (LocalLayout.persistentRefs original width) path.2.2
  have narrowBound := (narrowCount.le.trans (narrow_total_le _))
  omega

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
