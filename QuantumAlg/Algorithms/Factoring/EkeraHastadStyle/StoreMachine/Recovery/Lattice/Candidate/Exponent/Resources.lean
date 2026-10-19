/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Exponent.Correctness

/-!
# Actual candidate-exponent native resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat}

/-- Independent native formula for the original exponent copy and six Boolean operations. -/
def suffixTrace (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .not)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.bit .and))]

/-- Independent sign-dependent native formula for normalization and original range checks. -/
def exponentTrace (width : Nat) (negative : Bool) : List (Resource.Event model) :=
  (signTrace (model := model) width ++ magnitudeTrace (model := model) width negative) ++
    suffixTrace (model := model) width

/-- The actual suffix emits all seven independently specified native instructions. -/
lemma suffixInto_events (refs : Refs ctx width) (path : (suffixInto refs).Path) :
    (suffixInto refs).eventTrace path = suffixTrace (model := model) width := by
  change (BitWord.instruction (execution := model) (copyOp refs)).eventTrace path.1 ++
    ((BitWord.instruction (execution := model) (equalOp refs)).eventTrace path.2.1 ++
      ((BitWord.instruction (execution := model) (positiveOp refs)).eventTrace path.2.2.1 ++
        ((BitWord.instruction (execution := model) (belowOp refs)).eventTrace path.2.2.2.1 ++
          ((BitWord.instruction (execution := model) (nonnegativeOp refs)).eventTrace
            path.2.2.2.2.1 ++
            ((BitWord.instruction (execution := model) (rangeOp refs)).eventTrace
              path.2.2.2.2.2.1 ++
              (BitWord.instruction (execution := model) (acceptedOp refs)).eventTrace
                path.2.2.2.2.2.2))))) = _
  rw [BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace, BitWord.bitWord_instruction_eventTrace,
    BitWord.bitWord_instruction_eventTrace]
  rfl

/-- Every actual chosen classifier path has the original checks after its selected magnitude arm. -/
lemma candidateExponentInto_events (refs : Refs ctx width)
    (path : (candidateExponentInto refs).Path) :
    (candidateExponentInto refs).eventTrace path =
      exponentTrace (model := model) width path.1.2.1.toBool :=
  congrArg₂ List.append
    (normalizeMagnitude_events (candidateInput refs) refs.negative refs.magnitude path.1)
    (suffixInto_events refs path.2)

/-- The actual native trace selects the sign computed from the original candidate word. -/
lemma candidateExponentInto_actualEvents (refs : Refs ctx width) (store : Store ctx) :
    (candidateExponentInto refs).eventTrace (exponentStep refs store).2 =
      exponentTrace (model := model) width (rawIsNegative (store.read (candidateInput refs))) :=
  congrArg₂ List.append
    (normalizeMagnitude_actualEvents (candidateInput refs) refs.negative refs.magnitude store)
    (suffixInto_events refs _)

/-- Actual native multiplicities count precisely the real sign-selected arithmetic and checks. -/
lemma candidateExponentInto_resourcePool (refs : Refs ctx width)
    (path : (candidateExponentInto refs).Path) :
    (candidateExponentInto refs).resourcePool path =
      ResourcePool.ofList (exponentTrace (model := model) width path.1.2.1.toBool) :=
  congrArg ResourcePool.ofList (candidateExponentInto_events refs path)

/-- The actual suffix contains exactly seven native instructions. -/
lemma suffixInto_eventCount (refs : Refs ctx width) (path : (suffixInto refs).Path) :
    ((suffixInto refs).eventTrace path).length = 7 := by
  rw [suffixInto_events]
  rfl

/-- The full actual classifier meets the independent ten-instruction upper bound. -/
lemma candidateExponentInto_eventCount_le (refs : Refs ctx width)
    (path : (candidateExponentInto refs).Path) :
    ((candidateExponentInto refs).eventTrace path).length ≤ 10 := by
  change List.length ((_ : List (Resource.Event model)) ++ _) ≤ _
  rw [List.length_append, suffixInto_eventCount]
  have bound := normalizeMagnitude_eventCount_le
    (candidateInput refs) refs.negative refs.magnitude path.1
  dsimp only [normalizeInto]
  omega

/-- The suffix's unit-duration depth charges all original data-dependent checks. -/
lemma suffixInto_depth (refs : Refs ctx width) (path : (suffixInto refs).Path) :
    (suffixInto refs).depth (fun _ => 1) path = 7 := by
  rcases path with ⟨a, b, c, d, e, f, g⟩
  simp only [suffixInto, Circuit.depth_seq, BitWord.bitWord_instruction_depth]

/-- Unit-duration depth includes the sign-to-magnitude dependency and every original suffix step. -/
lemma candidateExponentInto_depth_le (refs : Refs ctx width)
    (path : (candidateExponentInto refs).Path) :
    (candidateExponentInto refs).depth (fun _ => 1) path ≤ 10 := by
  change (normalizeInto refs).depth (fun _ => 1) path.1 +
    (suffixInto refs).depth (fun _ => 1) path.2 ≤ _
  rw [suffixInto_depth]
  have bound := normalizeMagnitude_depth_le
    (candidateInput refs) refs.negative refs.magnitude path.1
  dsimp only [normalizeInto]
  omega

/-- The original seven actual suffix instructions restore the borrowed-reference joint state. -/
lemma suffixInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (suffixInto refs).BorrowedRestored Reference state
      ((suffixInto refs).execute environment Reference state) := by
  refine Circuit.borrowedRestored_seq (environment := environment)
    (BitWord.instruction (execution := model) (copyOp refs)) _ _
    (Circuit.borrowedRestored_classical (environment := environment) _ _) ?_
  refine Circuit.borrowedRestored_seq (environment := environment)
    (BitWord.instruction (execution := model) (equalOp refs)) _ _
    (Circuit.borrowedRestored_classical (environment := environment) _ _) ?_
  refine Circuit.borrowedRestored_seq (environment := environment)
    (BitWord.instruction (execution := model) (positiveOp refs)) _ _
    (Circuit.borrowedRestored_classical (environment := environment) _ _) ?_
  refine Circuit.borrowedRestored_seq (environment := environment)
    (BitWord.instruction (execution := model) (belowOp refs)) _ _
    (Circuit.borrowedRestored_classical (environment := environment) _ _) ?_
  refine Circuit.borrowedRestored_seq (environment := environment)
    (BitWord.instruction (execution := model) (nonnegativeOp refs)) _ _
    (Circuit.borrowedRestored_classical (environment := environment) _ _) ?_
  refine Circuit.borrowedRestored_seq (environment := environment)
    (BitWord.instruction (execution := model) (rangeOp refs)) _ _
    (Circuit.borrowedRestored_classical (environment := environment) _ _) ?_
  exact Circuit.borrowedRestored_classical (environment := environment) _ _

/-- The entire actual classifier restores every borrowed correlation for arbitrary references. -/
lemma candidateExponentInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidateExponentInto refs).BorrowedRestored Reference state
      ((candidateExponentInto refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (normalizeMagnitude_borrowedRestored (model := model)
      (candidateInput refs) refs.negative refs.magnitude
      Reference state)
    (suffixInto_borrowedRestored refs Reference _)

/-- Every actual suffix instruction retains the original quantum and classical context. -/
lemma suffixInto_visited (refs : Refs ctx width) (path : (suffixInto refs).Path) :
    (suffixInto refs).visitedContexts path = List.replicate 7 ctx := rfl

/-- Both actual sign-selected arms and all suffix operations retain the supplied context. -/
lemma candidateExponentInto_visited (refs : Refs ctx width)
    (path : (candidateExponentInto refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (candidateExponentInto refs).visitedContexts path) : visited = ctx := by
  change visited ∈ (normalizeInto refs).visitedContexts path.1 ++
    (suffixInto refs).visitedContexts path.2 at present
  rcases List.mem_append.mp present with normalized | suffix
  · change visited ∈ (normalizeMagnitude _ _ _).visitedContexts path.1 at normalized
    rw [normalizeMagnitude_visited (model := model)
      (candidateInput refs) refs.negative refs.magnitude
      path.1] at normalized
    split at normalized <;>
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using normalized
  · rw [suffixInto_visited refs path.2] at suffix
    exact (List.mem_replicate.mp suffix).2

/-- Actual classifier resident accounting retains every pre-existing caller resource. -/
lemma candidateExponentInto_resident_le (refs : Refs ctx width)
    (path : (candidateExponentInto refs).Path) :
    (candidateExponentInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [candidateExponentInto_visited refs path visited present]

/-- The classifier allocates no new cells, while all original supplied roles remain counted. -/
lemma candidateExponentInto_auxiliary_le (refs : Refs ctx width)
    (path : (candidateExponentInto refs).Path) :
    (candidateExponentInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [candidateExponentInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateExponent
