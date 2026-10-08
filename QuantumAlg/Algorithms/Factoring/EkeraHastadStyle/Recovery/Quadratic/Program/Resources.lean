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

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width resultWidth : Nat}

/-- The two actual initialization labels load one after the candidates have been materialized. -/
def programOneEvents (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor (RSA.quadraticWordWidth width))),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .increment (RSA.quadraticWordWidth width)))]

/-- Independent native coordinate allowance for the complete actual scoped program. -/
def programNativeEnvelope (width resultWidth : Nat) : ResourcePool model :=
  (nativeEnvelope (model := model) width +
    ResourcePool.ofList (programOneEvents (model := model) width)) +
    (Pair.nativeEnvelope (model := model) (RSA.quadraticWordWidth width) +
      NarrowSelection.nativeEnvelope (model := model) (RSA.quadraticWordWidth width) resultWidth)

/-- All actual scopes retain exactly the chronological traces of the four executed blocks. -/
theorem nativeQuadratic_program_eventTrace (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (path : (program (model := model) input modulus original).Path) :
    (program (model := model) input modulus original).eventTrace path =
      ((candidates (model := model) (LocalLayout.arithmeticRead input width)
        (LocalLayout.arithmeticRead modulus width)
        (LocalLayout.arithmeticRefs ctx width)).eventTrace path.1.1 ++
          programOneEvents (model := model) width) ++
      ((Pair.code (model := model) (LocalLayout.pairRefs modulus)).eventTrace path.2.1 ++
        (NarrowSelection.code (model := model)
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
          (LocalLayout.persistentRefs original width)).eventTrace path.2.2) := by
  change ((candidates (model := model) (LocalLayout.arithmeticRead input width)
      (LocalLayout.arithmeticRead modulus width)
      (LocalLayout.arithmeticRefs ctx width)).eventTrace path.1.1 ++
    ((BitWord.instruction (execution := model)
      (CheckConstants.clearOp (LocalLayout.arithmeticRefs ctx width).center)).eventTrace
        path.1.2.1 ++
      (BitWord.instruction (execution := model)
        (CheckConstants.incrementOp (LocalLayout.arithmeticRefs ctx width).center)).eventTrace
          path.1.2.2)) ++
    ((Pair.code (model := model) (LocalLayout.pairRefs modulus)).eventTrace path.2.1 ++
      (NarrowSelection.code (model := model)
        (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
        (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
        (LocalLayout.persistentRefs original width)).eventTrace path.2.2) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

omit [BitWord.Selected model] in
private theorem pool_groups (first second third fourth : List (Resource.Event model)) :
    ResourcePool.ofList ((first ++ second) ++ (third ++ fourth)) =
      (ResourcePool.ofList first + ResourcePool.ofList second) +
        (ResourcePool.ofList third + ResourcePool.ofList fourth) := by
  rw [ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]

/-- The actual program ledger is precisely the sum of its four actual block ledgers. -/
theorem nativeQuadratic_program_resourcePool (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (path : (program (model := model) input modulus original).Path) :
    (program (model := model) input modulus original).resourcePool path =
      ((candidates (model := model) (LocalLayout.arithmeticRead input width)
        (LocalLayout.arithmeticRead modulus width)
        (LocalLayout.arithmeticRefs ctx width)).resourcePool path.1.1 +
          ResourcePool.ofList (programOneEvents (model := model) width)) +
      ((Pair.code (model := model) (LocalLayout.pairRefs modulus)).resourcePool path.2.1 +
        (NarrowSelection.code (model := model)
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
          (LocalLayout.persistentRefs original width)).resourcePool path.2.2) :=
  (congrArg ResourcePool.ofList
    (nativeQuadratic_program_eventTrace input modulus original path)).trans
    (pool_groups _ _ _ _)

/-- Every actual event coordinate is dominated by the independent complete-program allowance. -/
theorem nativeQuadratic_program_pool_le (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (path : (program (model := model) input modulus original).Path) :
    (program (model := model) input modulus original).resourcePool path ≤
      programNativeEnvelope (model := model) width resultWidth := by
  have actual := nativeQuadratic_program_resourcePool (model := model) input modulus original path
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
theorem nativeQuadratic_program_nativeEnvelope_card
    (width resultWidth : Nat) :
    (programNativeEnvelope (model := model) width resultWidth).card =
      7 * RSA.quadraticWordWidth width + 39 := by
  rw [programNativeEnvelope, Multiset.card_add, Multiset.card_add, Multiset.card_add,
    nativeQuadratic_nativeEnvelope_card, Pair.nativeQuadratic_pair_nativeEnvelope_card,
    NarrowSelection.nativeQuadratic_narrow_nativeEnvelope_card]
  have oneCount : (ResourcePool.ofList (programOneEvents (model := model) width)).card = 2 := rfl
  rw [oneCount]

omit [BitWord.Selected model] in
private theorem count_groups (first second third fourth : ResourcePool model) :
    ((first + second) + (third + fourth)).card =
      (first.card + second.card) + (third.card + fourth.card) := by
  simp only [Multiset.card_add]

private theorem narrow_total_le (taken : Bool) : (if taken then 5 else 3) ≤ 5 := by
  cases taken <;> decide

/-- The actual event total counts only the subtraction and selector arms actually executed. -/
theorem nativeQuadratic_program_eventCount_le (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (path : (program (model := model) input modulus original).Path) :
    ((program (model := model) input modulus original).resourcePool path).card ≤
      7 * RSA.quadraticWordWidth width + 37 := by
  have count := (congrArg (fun pool : ResourcePool model => pool.card)
    (nativeQuadratic_program_resourcePool input modulus original path)).trans
      (count_groups _ _ _ _)
  have candidatesBound := nativeQuadratic_candidates_eventCount_le (model := model)
    (LocalLayout.arithmeticRead input width) (LocalLayout.arithmeticRead modulus width)
    (LocalLayout.arithmeticRefs ctx width) path.1.1
  have pairBound := (Pair.nativeQuadratic_pair_total_le (model := model)
    (LocalLayout.pairRefs modulus) path.2.1).1
  have narrowCount := NarrowSelection.nativeQuadratic_narrow_eventCount (model := model)
    (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
    (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
    (LocalLayout.persistentRefs original width) path.2.2
  have narrowBound := (narrowCount.le.trans (narrow_total_le _))
  have oneCount : (ResourcePool.ofList (programOneEvents (model := model) width)).card = 2 := rfl
  omega

/-- Unit-duration depth follows the identical actual serial block order through every scope. -/
theorem nativeQuadratic_program_unitDepth_le (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (path : (program (model := model) input modulus original).Path) :
    (program (model := model) input modulus original).depth (fun _ => 1) path ≤
      7 * RSA.quadraticWordWidth width + 37 := by
  have count : (program (model := model) input modulus original).depth (fun _ => 1) path =
      ((candidates (model := model) (LocalLayout.arithmeticRead input width)
        (LocalLayout.arithmeticRead modulus width) (LocalLayout.arithmeticRefs ctx width)).depth
          (fun _ => 1) path.1.1 + 2) +
      ((Pair.code (model := model) (LocalLayout.pairRefs modulus)).depth (fun _ => 1) path.2.1 +
        (NarrowSelection.code (model := model)
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
          (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
          (LocalLayout.persistentRefs original width)).depth (fun _ => 1) path.2.2) := rfl
  have candidatesBound := nativeQuadratic_candidates_unitDepth_le (model := model)
    (LocalLayout.arithmeticRead input width) (LocalLayout.arithmeticRead modulus width)
    (LocalLayout.arithmeticRefs ctx width) path.1.1
  have pairBound := (Pair.nativeQuadratic_pair_total_le (model := model)
    (LocalLayout.pairRefs modulus) path.2.1).2
  have narrowCount := NarrowSelection.nativeQuadratic_narrow_unitDepth (model := model)
    (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.accepted)
    (FirstAccepted.cellRead (LocalLayout.pairRefs modulus).selection.selected)
    (LocalLayout.persistentRefs original width) path.2.2
  have narrowBound := (narrowCount.le.trans (narrow_total_le _))
  omega

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
