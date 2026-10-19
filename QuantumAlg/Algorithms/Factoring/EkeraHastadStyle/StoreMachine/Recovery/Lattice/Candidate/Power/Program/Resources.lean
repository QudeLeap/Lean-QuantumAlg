/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Program.Correctness
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Space

/-!
# Actual candidate modular-power resources
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePowerMachine

open Execution
open ClassicalAlgorithms.Modular
open ClassicalRoutines.Modular.NativePower

noncomputable section

variable {model : ExecutionModel}
  {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width exponentWidth : Nat}

/-- Independent shared native-power allowance followed by the original equality test. -/
def candidatePowerEventEnvelope (model : ExecutionModel) [BitWord.Selected model]
    (width exponentWidth : Nat) : ResourcePool model :=
  eventEnvelope model width exponentWidth +
    ResourcePool.singleton (.classicalOperation
      (BitWord.selectedCoordinate (execution := model) (.wordBinary .equal width)))

/-- The original target equality follows precisely the actual shared power path. -/
lemma candidatePowerInto_events (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).eventTrace path =
      (into spec refs.generator refs.exponent refs.power).eventTrace path.1 ++
        [.classicalOperation
          (BitWord.selectedCoordinate (execution := model) (.wordBinary .equal width))] := by
  change _ ++ (BitWord.instruction (execution := model) (equalityOp refs)).eventTrace path.2 = _
  rw [BitWord.bitWord_instruction_eventTrace]
  rfl

/-- The actual native pool contains the selected power instructions and one actual equality. -/
lemma candidatePowerInto_resourcePool (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).resourcePool path =
      (into spec refs.generator refs.exponent refs.power).resourcePool path.1 +
        ResourcePool.singleton (.classicalOperation
          (BitWord.selectedCoordinate (execution := model) (.wordBinary .equal width))) := by
  change ResourcePool.ofList ((candidatePowerInto spec refs).eventTrace path) = _
  rw [candidatePowerInto_events, ResourcePool.ofList_append]
  simp only [ResourcePool.ofList_cons, ResourcePool.ofList_nil, add_zero]
  rfl

/-- Actual native multiplicities fit the independent complete powering and comparison budget. -/
lemma candidatePowerInto_pool_le (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).resourcePool path ≤
      candidatePowerEventEnvelope model width exponentWidth := by
  rw [candidatePowerInto_resourcePool]
  exact add_le_add (nativePower_into_pool_le spec refs.generator refs.exponent refs.power path.1)
    le_rfl

/-- The actual dependency depth counts every initialization, selected multiply and final test. -/
lemma candidatePowerInto_depth_le (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (duration : Resource.Event model → Nat)
    (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).depth duration path ≤
      depthBound width exponentWidth duration +
        duration (.classicalOperation
          (BitWord.selectedCoordinate (execution := model) (.wordBinary .equal width))) := by
  change (into spec refs.generator refs.exponent refs.power).depth duration path.1 +
    (BitWord.instruction (execution := model) (equalityOp refs)).depth duration path.2 ≤ _
  rw [BitWord.bitWord_instruction_depth]
  exact Nat.add_le_add_right
    (nativePower_into_depth_le spec refs.generator refs.exponent refs.power duration path.1) _

/-- Unit native durations meet the original source width's independent complete step bound. -/
lemma candidatePowerInto_unitDepth_le (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).depth (fun _ => 1) path ≤
      2 * width + 6 + 6 * exponentWidth := by
  have actual := nativePower_into_unitDepth_le spec refs.generator refs.exponent refs.power path.1
  change (into spec refs.generator refs.exponent refs.power).depth (fun _ => 1) path.1 +
    (BitWord.instruction (execution := model) (equalityOp refs)).depth (fun _ => 1)
      path.2 ≤ _
  rw [BitWord.bitWord_instruction_depth]
  omega

/-- Actual power scopes, selected arithmetic and equality restore all borrowed correlations. -/
lemma candidatePowerInto_borrowedRestored (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidatePowerInto spec refs).BorrowedRestored Reference state
      ((candidatePowerInto spec refs).execute environment Reference state) :=
  Circuit.borrowedRestored_seq (environment := environment) _ _ state
    (nativePower_into_borrowedRestored spec refs.generator refs.exponent refs.power Reference state)
    (Circuit.borrowedRestored_classical (environment := environment) _ _)

/-- The actual final equality retains the original supplied resident context. -/
lemma equality_resident_le (refs : Refs ctx width exponentWidth)
    (path : (BitWord.instruction (execution := model) (equalityOp refs)).Path) :
    (BitWord.instruction (execution := model) (equalityOp refs)).peakResidentSpace path ≤
      ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  change visited ∈ [ctx] at present
  rw [List.mem_singleton.mp present]

/-- The actual final equality retains the original supplied auxiliary roles. -/
lemma equality_auxiliary_le (refs : Refs ctx width exponentWidth)
    (path : (BitWord.instruction (execution := model) (equalityOp refs)).Path) :
    (BitWord.instruction (execution := model) (equalityOp refs)).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  change visited ∈ [ctx] at present
  rw [List.mem_singleton.mp present]

/-- Resident peak counts all original caller storage and the real lexical power scratch. -/
lemma candidatePowerInto_resident_le (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).peakResidentSpace path ≤
      ctx.residentSpace + powerSpace model.kind width := by
  refine (Circuit.peakResidentSpace_seq (powerInto spec refs)
    (BitWord.instruction (execution := model) (equalityOp refs)) path).le.trans ?_
  apply SpacePool.max_le
  · exact nativePower_into_resident_le spec refs.generator refs.exponent refs.power path.1
  · exact (equality_resident_le refs path.2).trans (le_add_of_nonneg_right zero_le)

/-- Every actual temporary power bit remains charged as auxiliary at its simultaneous peak. -/
lemma candidatePowerInto_auxiliary_le (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (path : (candidatePowerInto spec refs).Path) :
    (candidatePowerInto spec refs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + powerSpace model.kind width := by
  refine (Circuit.peakAuxiliarySpace_seq (powerInto spec refs)
    (BitWord.instruction (execution := model) (equalityOp refs)) path).le.trans ?_
  apply SpacePool.max_le
  · exact nativePower_into_auxiliary_le spec refs.generator refs.exponent refs.power path.1
  · exact (equality_auxiliary_le refs path.2).trans (le_add_of_nonneg_right zero_le)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePowerMachine
