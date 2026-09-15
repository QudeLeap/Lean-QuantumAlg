/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Program

/-!
# Independent native instruction formulas for fixed-fuel LLL

The formulas use only the original word width and Boolean decisions. Reading
these decisions from a circuit path then recovers that path's exact ordered
native events, including phase writes and the six-entry Gram refresh.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Complete decision data for one terminal, first-pair, or second-pair iteration. -/
inductive StepDecisions where
  | done
  | first (magnitude correction restore pairPasses advance : Bool)
  | second (magnitude32 correction32 restore32 magnitude31 correction31 restore31
      pairPasses finish : Bool)

/-- The first phase writes its latch only when its recorded decision requests an advance. -/
def firstAdvanceTrace (advance : Bool) : List (Resource.Event kind) :=
  if advance then [.classicalOperation (.bit .not)] else []

/-- The second phase always writes its selected finish or restart latch. -/
def secondAdvanceTrace (finish : Bool) : List (Resource.Event kind) :=
  [.classicalOperation (.bit (if finish then .not else .xor))]

/-- Independent original instruction formula for each complete phase and its recorded decisions. -/
def stepTrace (width : Nat) : StepDecisions → List (Resource.Event kind)
  | .done => []
  | .first magnitude correction restore pairPasses advance =>
      LatticeFirstPairMachine.firstPairTrace width magnitude correction restore pairPasses ++
        (firstAdvanceTrace advance ++ LatticeMetricMachine.gramTrace width)
  | .second magnitude32 correction32 restore32 magnitude31 correction31 restore31 pairPasses
    finish =>
      LatticeSecondPairFullMachine.secondPairTrace width magnitude32 correction32 restore32
        magnitude31 correction31 restore31 pairPasses ++
          (secondAdvanceTrace finish ++ LatticeMetricMachine.gramTrace width)

/-- Read only the Boolean decisions recorded by an actual first-driver path. -/
def firstDecisions (refs : Refs ctx width) (path : (firstStepInto refs).Path) : StepDecisions :=
  let pair := path.1
  .first pair.1.1.1.1.2.1.toBool pair.1.1.2.1.2.1.1.toBool pair.1.1.2.2.2.2.1.toBool
    pair.2.2.1.toBool path.2.1.1.toBool

/-- Read only the Boolean decisions recorded by an actual second-driver path. -/
def secondDecisions (refs : Refs ctx width) (path : (secondStepInto refs).Path) : StepDecisions :=
  let pair := path.1
  .second pair.1.1.2.1.1.1.2.1.toBool pair.1.1.2.1.2.1.2.1.1.toBool
    pair.1.1.2.1.2.2.2.2.1.toBool pair.1.2.2.1.1.1.2.1.toBool
    pair.1.2.2.1.2.1.2.1.1.toBool pair.1.2.2.1.2.2.2.2.1.toBool
    pair.2.2.2.2.1.toBool path.2.1.1.toBool

/-- Read the recorded pair-selection bit before its corresponding actual driver decisions. -/
def nonDoneDecisions (refs : Refs ctx width) (path : (nonDoneStepInto refs).Path) : StepDecisions :=
  match path with
  | ⟨.bit true, selected⟩ => secondDecisions refs selected
  | ⟨.bit false, selected⟩ => firstDecisions refs selected

/-- Read the recorded terminal bit before any nonterminal driver decisions. -/
def stepDecisions (refs : Refs ctx width) (path : (stepInto refs).Path) : StepDecisions :=
  match path with
  | ⟨.bit true, _⟩ => .done
  | ⟨.bit false, selected⟩ => nonDoneDecisions refs selected

/-- Independent chronological concatenation of the fixed number of original step formulas. -/
def fixedFuelTrace (fuel width : Nat) (decisions : Fin fuel → StepDecisions) :
    List (Resource.Event kind) :=
  (List.ofFn (fun index => stepTrace width (decisions index))).flatten

/-- Actual first-phase latch events equal their independent conditional-write formula. -/
theorem firstAdvanceInto_events (refs : Refs ctx width) (path : (firstAdvanceInto refs).Path) :
    (firstAdvanceInto refs).eventTrace path = firstAdvanceTrace path.1.toBool := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- Actual second-phase latch events equal their independent selected-write formula. -/
theorem secondAdvanceInto_events (refs : Refs ctx width) (path : (secondAdvanceInto refs).Path) :
    (secondAdvanceInto refs).eventTrace path = secondAdvanceTrace path.1.toBool := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag => cases flag <;> rfl

/-- The complete actual first driver emits the independent formula at its recorded decisions. -/
theorem firstStepInto_events (refs : Refs ctx width) (path : (firstStepInto refs).Path) :
    (firstStepInto refs).eventTrace path = stepTrace width (firstDecisions refs path) := by
  change _ ++ (_ ++ _) = _
  rw [LatticeFirstPairMachine.firstPairInto_events, firstAdvanceInto_events,
    LatticeMetricMachine.refreshInto_events]
  rfl

/-- The complete actual second driver emits the independent formula at its recorded decisions. -/
theorem secondStepInto_events (refs : Refs ctx width) (path : (secondStepInto refs).Path) :
    (secondStepInto refs).eventTrace path = stepTrace width (secondDecisions refs path) := by
  change _ ++ (_ ++ _) = _
  rw [LatticeSecondPairFullMachine.secondPairInto_events, secondAdvanceInto_events,
    LatticeMetricMachine.refreshInto_events]
  rfl

/-- The actual selected nonterminal arm emits its corresponding independent step formula. -/
theorem nonDoneStepInto_events (refs : Refs ctx width) (path : (nonDoneStepInto refs).Path) :
    (nonDoneStepInto refs).eventTrace path = stepTrace width (nonDoneDecisions refs path) := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · exact firstStepInto_events refs path
    · exact secondStepInto_events refs path

/-- Every actual iteration emits exactly the independent formula at its recorded decisions. -/
theorem stepInto_events (refs : Refs ctx width) (path : (stepInto refs).Path) :
    (stepInto refs).eventTrace path = stepTrace width (stepDecisions refs path) := by
  rcases path with ⟨flag, path⟩
  cases flag with
  | bit flag =>
    cases flag
    · exact nonDoneStepInto_events refs path
    · rfl

/-- Native multiplicities of one actual iteration come from the independent instruction formula. -/
theorem stepInto_resourcePool (refs : Refs ctx width) (path : (stepInto refs).Path) :
    (stepInto refs).resourcePool path = ResourcePool.ofList (stepTrace width (stepDecisions refs
      path)) :=
  congrArg ResourcePool.ofList (stepInto_events refs path)

/-- Every actual run emits chronological independent step formulas at its own decisions. -/
theorem fixedFuelInto_events (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto fuel refs).Path) :
    (fixedFuelInto fuel refs).eventTrace path =
      fixedFuelTrace fuel width (fun index => stepDecisions refs (path index)) := by
  change (List.ofFn (fun index : Fin fuel => (stepInto refs).eventTrace (path index))).flatten = _
  simp only [stepInto_events, fixedFuelTrace]

/-- The actual complete resource pool equals the independently specified native multiplicities. -/
theorem fixedFuelInto_resourcePool (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto fuel refs).Path) :
    (fixedFuelInto fuel refs).resourcePool path = ResourcePool.ofList
      (fixedFuelTrace fuel width (fun index => stepDecisions refs (path index))) :=
  congrArg ResourcePool.ofList (fixedFuelInto_events fuel refs path)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
