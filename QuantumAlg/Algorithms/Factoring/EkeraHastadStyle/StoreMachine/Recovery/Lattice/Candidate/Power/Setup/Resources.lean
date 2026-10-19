/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup.Correctness

import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Space

/-!
# Actual shared modular-setup resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup

open Execution
open ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Independent native allowance for the original base packing and two constant materializations. -/
def prepareEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
      (.residueEncoding .pack width))) +
    (ClassicalRoutines.ConstantWord.envelope model (width + 1) +
      ClassicalRoutines.ConstantWord.envelope model width)

/-- Independent complete preparation and original shared target-power allowance. -/
def setupEventEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (width : Nat) : ResourcePool model :=
  prepareEnvelope model width +
    ClassicalRoutines.Modular.NativePower.eventEnvelope model width width

/-- Actual setup traces preserve the order from shared inputs to their consumed target power. -/
lemma setupInto_events (input : Input N) (refs : Refs ctx N)
    (path : (setupInto input refs).Path) :
    (setupInto input refs).eventTrace path =
      (prepareInto refs).eventTrace path.1 ++ (powerInto input refs).eventTrace path.2 := rfl

/-- Actual setup native multiplicities are exactly those of its actual preparation and power. -/
lemma setupInto_resourcePool (input : Input N) (refs : Refs ctx N)
    (path : (setupInto input refs).Path) :
    (setupInto input refs).resourcePool path =
      (prepareInto refs).resourcePool path.1 + (powerInto input refs).resourcePool path.2 :=
  ResourcePool.ofList_append _ _

/-- Actual base packing and full-width loaders satisfy the independent native allowance. -/
lemma prepareInto_pool_le (refs : Refs ctx N) (path : (prepareInto refs).Path) :
    (prepareInto refs).resourcePool path ≤ prepareEnvelope model (modulusBits N) := by
  rw [show (prepareInto refs).resourcePool path =
      ResourcePool.ofList ((prepareInto refs).eventTrace path) from rfl]
  change ResourcePool.ofList ((BitWord.instruction (execution := model)
    (packOp refs)).eventTrace path.1 ++ (_ ++ _)) ≤ _
  rw [BitWord.bitWord_instruction_eventTrace]
  simp only [ResourcePool.ofList_append, ResourcePool.ofList_cons, ResourcePool.ofList_nil,
    add_zero, prepareEnvelope]
  exact add_le_add le_rfl
    (add_le_add (ClassicalRoutines.ConstantWord.constantWord_pool_le refs.modulus N path.2.1)
      (ClassicalRoutines.ConstantWord.constantWord_pool_le refs.targetExponent
        (RSA.targetExponent N) path.2.2))

/-- The actual complete setup fits the independently specified preparation and power budget. -/
lemma setupInto_pool_le (input : Input N) (refs : Refs ctx N)
    (path : (setupInto input refs).Path) :
    (setupInto input refs).resourcePool path ≤ setupEventEnvelope model (modulusBits N) := by
  rw [setupInto_resourcePool]
  exact add_le_add (prepareInto_pool_le refs path.1)
    (ClassicalRoutines.Modular.NativePower.nativePower_into_pool_le (modulusSpec input)
      (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower path.2)

/-- Actual preparation charges base packing and every selected increment after every shift. -/
lemma prepareInto_depth_le (refs : Refs ctx N) (path : (prepareInto refs).Path) :
    (prepareInto refs).depth (fun _ => 1) path ≤ 4 * modulusBits N + 3 := by
  have modulusDepth := ClassicalRoutines.ConstantWord.constantWord_depth_le refs.modulus N
    (fun _ => 1) path.2.1
  have exponentDepth := ClassicalRoutines.ConstantWord.constantWord_depth_le refs.targetExponent
    (RSA.targetExponent N) (fun _ => 1) path.2.2
  change 1 + ((modulusInto refs).depth (fun _ => 1) path.2.1 +
    (exponentInto refs).depth (fun _ => 1) path.2.2) ≤ _
  dsimp only [modulusInto, exponentInto]
  omega

/-- The actual full setup includes the original width-many target-power steps in its depth. -/
lemma setupInto_depth_le (input : Input N) (refs : Refs ctx N)
    (path : (setupInto input refs).Path) :
    (setupInto input refs).depth (fun _ => 1) path ≤ 12 * modulusBits N + 8 := by
  have prepared := prepareInto_depth_le refs path.1
  have powered := ClassicalRoutines.Modular.NativePower.nativePower_into_unitDepth_le
    (modulusSpec input) (writeInput refs.generator) (writeInput refs.targetExponent)
    refs.targetPower path.2
  change (prepareInto refs).depth (fun _ => 1) path.1 +
    (powerInto input refs).depth (fun _ => 1) path.2 ≤ _
  dsimp only [powerInto]
  omega

/-- Actual base packing and both constant loaders restore every borrowed correlation. -/
lemma prepareInto_borrowedRestored (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (prepareInto refs).BorrowedRestored Reference state
      ((prepareInto refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq
    (environment := environment) _ _ state (Circuit.borrowedRestored_classical (environment :=
    environment) _ state)
    (Circuit.borrowedRestored_seq (environment := environment) _ _ _
      (ClassicalRoutines.ConstantWord.constantWord_fold_borrowedRestored refs.modulus _ Reference _)
      (ClassicalRoutines.ConstantWord.constantWord_fold_borrowedRestored refs.targetExponent _
        Reference _))

/-- Actual shared setup restores the entire borrowed-reference joint state. -/
lemma setupInto_borrowedRestored (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (setupInto input refs).BorrowedRestored Reference state
      ((setupInto input refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq
    (environment := environment) _ _ state (prepareInto_borrowedRestored refs Reference state)
    (ClassicalRoutines.Modular.NativePower.nativePower_into_borrowedRestored (modulusSpec input)
      (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower Reference _)

/-- Every actual preparation operation retains the original caller context. -/
lemma prepareInto_visited (refs : Refs ctx N) (path : (prepareInto refs).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (prepareInto refs).visitedContexts path) :
    visited = ctx := by
  change visited ∈ [ctx] ++ ((modulusInto refs).visitedContexts path.2.1 ++
    (exponentInto refs).visitedContexts path.2.2) at present
  simp only [List.mem_append, List.mem_singleton] at present
  rcases present with packed | loaded | exponent
  · exact packed
  · exact ClassicalRoutines.ConstantWord.constantWord_fold_visited refs.modulus _
      path.2.1 visited loaded
  · exact ClassicalRoutines.ConstantWord.constantWord_fold_visited refs.targetExponent _
      path.2.2 visited exponent

/-- Actual preparation keeps every original resident resource counted. -/
lemma prepareInto_resident_le (refs : Refs ctx N) (path : (prepareInto refs).Path) :
    (prepareInto refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [prepareInto_visited refs path visited present]

/-- Actual preparation retains all original auxiliary roles without allocation. -/
lemma prepareInto_auxiliary_le (refs : Refs ctx N) (path : (prepareInto refs).Path) :
    (prepareInto refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [prepareInto_visited refs path visited present]

/-- The actual setup peak counts all caller storage and simultaneous real target-power scratch. -/
lemma setupInto_resident_le (input : Input N) (refs : Refs ctx N)
    (path : (setupInto input refs).Path) :
    (setupInto input refs).peakResidentSpace path ≤ ctx.residentSpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq (prepareInto refs)
    (powerInto input refs) path).le.trans ?_
  apply SpacePool.max_le
  · exact (prepareInto_resident_le refs path.1).trans (le_add_of_nonneg_right zero_le)
  · exact ClassicalRoutines.Modular.NativePower.nativePower_into_resident_le (modulusSpec input)
      (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower path.2

/-- Every live target-power temporary is included with all original auxiliary storage. -/
lemma setupInto_auxiliary_le (input : Input N) (refs : Refs ctx N)
    (path : (setupInto input refs).Path) :
    (setupInto input refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace +
      ClassicalRoutines.Modular.NativePower.powerSpace model.kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq (prepareInto refs)
    (powerInto input refs) path).le.trans ?_
  apply SpacePool.max_le
  · exact (prepareInto_auxiliary_le refs path.1).trans (le_add_of_nonneg_right zero_le)
  · exact ClassicalRoutines.Modular.NativePower.nativePower_into_auxiliary_le (modulusSpec input)
      (writeInput refs.generator) (writeInput refs.targetExponent) refs.targetPower path.2

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidateModularSetup
