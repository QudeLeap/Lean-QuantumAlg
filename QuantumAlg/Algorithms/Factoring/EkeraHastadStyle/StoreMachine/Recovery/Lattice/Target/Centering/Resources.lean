/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Centering.Correctness

/-!
# Native resources of actual centered-target selection

Five native preparation operations precede one subtraction or two-operation
negation. The selected trace, its coordinate envelope and the seven-operation
bound account for actual scratch initialization and retain the entire context.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget

open Execution
open ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent native scratch initialization and comparison formula. -/
def prepareTrace (width : Nat) : List (Resource.Event model) :=
  [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .bitXor width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .equal width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model) (.wordUnary .copy width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .shiftRight width)),
    .classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordBinary .lessThan width))]

/-- Independent selected subtraction or complement/increment formula. -/
def arithmeticTrace (width : Nat) (negates : Bool) : List (Resource.Event model) :=
  if negates then
    [.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.wordUnary .complement width)),
      .classicalOperation (BitWord.selectedCoordinate (execution := model)
        (.wordUnary .increment width))]
  else [.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordBinary .sub width))]

/-- The actual branch path selects negation precisely in the nonzero below-half arm. -/
def selectedNegation (refs : Refs ctx width) (path : (finishInto refs).Path) : Bool :=
  match path with
  | ⟨.bit true, _⟩ => false
  | ⟨.bit false, selected⟩ => selected.1.toBool

/-- Independent native formula for the complete centered-target call. -/
def centeredTrace (width : Nat) (negates : Bool) : List (Resource.Event model) :=
  prepareTrace width ++ arithmeticTrace width negates

private lemma prepare_events (refs : Refs ctx width) (path : (prepareInto refs).Path) :
    (prepareInto refs).eventTrace path = prepareTrace width := by
  change _ ++ (_ ++ (_ ++ (_ ++ _))) = _
  simp only [BitWord.bitWord_instruction_eventTrace]
  rfl

private lemma finish_events (refs : Refs ctx width) (path : (finishInto refs).Path) :
    (finishInto refs).eventTrace path = arithmeticTrace width (selectedNegation refs path) := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · rcases path with ⟨flag, path⟩
      cases flag with
      | bit flag =>
        cases flag
        · dsimp only [halfArm] at path ⊢
          change (BitWord.instruction (execution := model)
            (subOp refs refs.modulus refs.a)).eventTrace path = _
          rw [BitWord.bitWord_instruction_eventTrace]
          rfl
        · change (negateInto refs).eventTrace path = _
          change _ ++ _ = _
          rw [BitWord.bitWord_instruction_eventTrace,
            BitWord.bitWord_instruction_eventTrace]
          rfl
    · dsimp only [finishArm] at path ⊢
      change (BitWord.instruction (execution := model)
        (subOp refs refs.a refs.a)).eventTrace path = _
      rw [BitWord.bitWord_instruction_eventTrace]
      rfl

/-- Every actual path emits the exact independent native centered-target formula. -/
lemma centeredTargetInto_events (refs : Refs ctx width)
    (path : (centeredTargetInto refs).Path) :
    (centeredTargetInto refs).eventTrace path =
      centeredTrace width (selectedNegation refs path.2) :=
  congrArg₂ List.append (prepare_events refs path.1) (finish_events refs path.2)

/-- Actual centered-target multiplicities equal the selected native formula. -/
lemma centeredTargetInto_resourcePool (refs : Refs ctx width)
    (path : (centeredTargetInto refs).Path) :
    (centeredTargetInto refs).resourcePool path =
      ResourcePool.ofList (centeredTrace width (selectedNegation refs path.2)) :=
  congrArg ResourcePool.ofList (centeredTargetInto_events refs path)

/-- Placement-independent coordinate envelope covering either selected arithmetic arm. -/
def eventEnvelope (width : Nat) : ResourcePool model :=
  ResourcePool.ofList (prepareTrace width) +
    (ResourcePool.ofList (arithmeticTrace width false) +
      ResourcePool.ofList (arithmeticTrace width true))

/-- Every actual centered-target pool lies in the independent native coordinate envelope. -/
lemma centeredTargetInto_resourcePool_le (refs : Refs ctx width)
    (path : (centeredTargetInto refs).Path) :
    (centeredTargetInto refs).resourcePool path ≤ eventEnvelope width := by
  rw [centeredTargetInto_resourcePool, centeredTrace, ResourcePool.ofList_append]
  apply add_le_add le_rfl
  cases selectedNegation refs path.2
  · exact le_add_of_nonneg_right zero_le
  · exact le_add_of_nonneg_left zero_le

/-- The complete actual centered-target call executes at most seven native operations. -/
lemma centeredTargetInto_eventCount_le (refs : Refs ctx width)
    (path : (centeredTargetInto refs).Path) :
    ((centeredTargetInto refs).eventTrace path).length ≤ 7 := by
  rw [centeredTargetInto_events]
  cases selectedNegation refs path.2 <;> simp [centeredTrace, prepareTrace, arithmeticTrace]

private lemma finish_depth (refs : Refs ctx width) (path : (finishInto refs).Path) :
    (finishInto refs).depth (fun _ => 1) path ≤ 2 := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · rcases path with ⟨flag, path⟩
      cases flag with
      | bit flag =>
        cases flag
        · change 1 ≤ 2
          omega
        · change 2 ≤ 2
          omega
    · change 1 ≤ 2
      omega

/-- Unit-duration depth includes the chronological comparisons and selected arithmetic. -/
lemma centeredTargetInto_depth_le (refs : Refs ctx width)
    (path : (centeredTargetInto refs).Path) :
    (centeredTargetInto refs).depth (fun _ => 1) path ≤ 7 := by
  have selected := finish_depth refs path.2
  change 5 + (finishInto refs).depth (fun _ => 1) path.2 ≤ 7
  omega

private lemma prepare_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (prepareInto refs).BorrowedRestored Reference state
      ((prepareInto refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (Circuit.borrowedRestored_classical (environment := environment) _ _)
    (Circuit.borrowedRestored_seq
      (environment := environment) _ _ _ (Circuit.borrowedRestored_classical (environment :=
      environment) _ _)
      (Circuit.borrowedRestored_seq
        (environment := environment) _ _ _ (Circuit.borrowedRestored_classical (environment :=
        environment) _ _)
        (Circuit.borrowedRestored_seq
          (environment := environment) _ _ _ (Circuit.borrowedRestored_classical (environment :=
          environment) _ _)
          (Circuit.borrowedRestored_classical (environment := environment) _ _))))

private lemma half_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (halfInto refs).BorrowedRestored Reference state
      ((halfInto refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_branch (environment := environment) _ _ Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact Circuit.borrowedRestored_classical (environment := environment) _ _
    · exact Circuit.borrowedRestored_seq (environment := environment) _ _ state
        (Circuit.borrowedRestored_classical
          (environment := environment) _ _) (Circuit.borrowedRestored_classical (environment :=
          environment) _ _)

private lemma finish_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (finishInto refs).BorrowedRestored Reference state
      ((finishInto refs).execute environment Reference state) := by
  apply Circuit.borrowedRestored_branch (environment := environment) _ _ Reference _ state
  intro flag History _ state
  cases flag with
  | bit flag =>
    cases flag
    · exact half_borrowedRestored refs Reference state
    · exact Circuit.borrowedRestored_classical (environment := environment) _ _

/-- Actual comparison and selected arithmetic restore every borrowed-reference correlation. -/
lemma centeredTargetInto_borrowedRestored (refs : Refs ctx width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (centeredTargetInto refs).BorrowedRestored Reference state
      ((centeredTargetInto refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq
    (environment := environment) _ _ state (prepare_borrowedRestored refs Reference state)
    (finish_borrowedRestored refs Reference _)

private lemma finish_visited (refs : Refs ctx width) (path : (finishInto refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (finishInto refs).visitedContexts path) :
    visited = ctx := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · rcases path with ⟨flag, path⟩
      cases flag with
      | bit flag =>
        cases flag
        · exact List.mem_singleton.mp present
        · change visited ∈ [ctx, ctx] at present
          simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using present
    · exact List.mem_singleton.mp present

/-- Every selected native instruction retains the complete original supplied context. -/
lemma centeredTargetInto_visited (refs : Refs ctx width)
    (path : (centeredTargetInto refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (centeredTargetInto refs).visitedContexts path) : visited = ctx := by
  change visited ∈ (_ ++ _) at present
  rcases List.mem_append.mp present with prepared | selected
  · change visited ∈ [ctx, ctx, ctx, ctx, ctx] at prepared
    simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using prepared
  · exact finish_visited refs path.2 visited selected

/-- The entire original resident context remains counted during actual centered-target loading. -/
lemma centeredTargetInto_resident_le (refs : Refs ctx width)
    (path : (centeredTargetInto refs).Path) :
    (centeredTargetInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [centeredTargetInto_visited refs path visited present]

/-- The entire original auxiliary context remains counted throughout each selected branch. -/
lemma centeredTargetInto_auxiliary_le (refs : Refs ctx width)
    (path : (centeredTargetInto refs).Path) :
    (centeredTargetInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [centeredTargetInto_visited refs path visited present]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeTarget
