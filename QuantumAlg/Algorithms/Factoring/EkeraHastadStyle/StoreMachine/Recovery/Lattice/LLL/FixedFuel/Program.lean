/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Program.Layout

/-!
# Actual fixed-fuel LLL driver

Each iteration reads its actual terminal and pair-selection bits. The chosen
pair computes its actual Lovasz decision, updates its actual phase latch, and
refreshes all six Gram entries before the next iteration.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The actual first Lovasz result selects its original advance or identity. -/
def firstAdvanceArm (refs : Refs ctx width) : CShape.Value .bit → Circuit model ctx ctx
  | .bit true => LatticePhaseControl.transitionInto refs.machine .firstPass
  | .bit false => .id ctx

/-- Actual store and path of the selected first-phase latch update. -/
def firstAdvanceArmStep (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (firstAdvanceArm refs flag).Path :=
  match flag with
  | .bit true => BitWord.instructionStep (execution := model)
      (LatticePhaseControl.transitionOp refs.machine .firstPass) store
  | .bit false => (store, ())

/-- Read the actual first Lovasz bit to select the phase update. -/
def firstAdvanceInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .branch (.storage refs.first.lovasz.passes.toCStorageRef) (firstAdvanceArm refs)

/-- The actual observed first Lovasz bit is retained in the selected path. -/
def firstAdvanceStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (firstAdvanceInto refs).Path :=
  let flag := store.read (.storage refs.first.lovasz.passes.toCStorageRef)
  let selected := firstAdvanceArmStep refs flag store
  (selected.1, ⟨flag, selected.2⟩)

/-- The actual second Lovasz result selects the original finish or restart write. -/
def secondAdvanceArm (refs : Refs ctx width) : CShape.Value .bit → Circuit model ctx ctx
  | .bit true => LatticePhaseControl.transitionInto refs.machine .secondPass
  | .bit false => LatticePhaseControl.transitionInto refs.machine .secondFail

/-- Actual store and path of the selected second-phase latch update. -/
def secondAdvanceArmStep (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (secondAdvanceArm refs flag).Path :=
  match flag with
  | .bit true => BitWord.instructionStep (execution := model)
      (LatticePhaseControl.transitionOp refs.machine .secondPass) store
  | .bit false => BitWord.instructionStep (execution := model)
      (LatticePhaseControl.transitionOp refs.machine .secondFail) store

/-- Read the actual second Lovasz bit to select the phase update. -/
def secondAdvanceInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .branch (.storage refs.second.branch.lovasz.passes.toCStorageRef) (secondAdvanceArm refs)

/-- The actual observed second Lovasz bit is retained in the selected path. -/
def secondAdvanceStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (secondAdvanceInto refs).Path :=
  let flag := store.read (.storage refs.second.branch.lovasz.passes.toCStorageRef)
  let selected := secondAdvanceArmStep refs flag store
  (selected.1, ⟨flag, selected.2⟩)

/-- The actual first phase update feeds a complete Gram refresh. -/
def firstTailInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (firstAdvanceInto refs)
    (LatticeMetricMachine.refreshInto (model := model) refs.machine.basis refs.metric)

/-- Actual first phase and Gram-refresh stores and paths. -/
def firstTailStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (firstTailInto refs).Path :=
  let advanced := firstAdvanceStep refs store
  (LatticeMetricMachine.refreshStore refs.machine.basis refs.metric advanced.1,
    (advanced.2, LatticeMetricMachine.refreshPath (model := model) refs.machine.basis
      refs.metric advanced.1))

/-- The actual first pair feeds its original phase selection and next Gram snapshot. -/
def firstStepInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeFirstPairMachine.firstPairInto (model := model) refs.first) (firstTailInto refs)

/-- The actual store and chronological path of the complete first-pair driver arm. -/
def firstStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (firstStepInto refs).Path :=
  let reduced := LatticeFirstPairMachine.firstPairStep (model := model) refs.first store
  let tail := firstTailStep refs reduced.1
  (tail.1, (reduced.2, tail.2))

/-- The actual second phase update feeds a complete Gram refresh. -/
def secondTailInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (secondAdvanceInto refs)
    (LatticeMetricMachine.refreshInto (model := model) refs.machine.basis refs.metric)

/-- Actual second phase and Gram-refresh stores and paths. -/
def secondTailStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (secondTailInto refs).Path :=
  let advanced := secondAdvanceStep refs store
  (LatticeMetricMachine.refreshStore refs.machine.basis refs.metric advanced.1,
    (advanced.2, LatticeMetricMachine.refreshPath (model := model) refs.machine.basis
      refs.metric advanced.1))

/-- The actual second pair feeds its original phase selection and next Gram snapshot. -/
def secondStepInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .seq (LatticeSecondPairFullMachine.secondPairInto (model := model) refs.second)
    (secondTailInto refs)

/-- The actual store and chronological path of the complete second-pair driver arm. -/
def secondStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (secondStepInto refs).Path :=
  let reduced := LatticeSecondPairFullMachine.secondPairStep (model := model) refs.second store
  let tail := secondTailStep refs reduced.1
  (tail.1, (reduced.2, tail.2))

/-- The actual phase bit selects the original first or second pair. -/
def nonDoneArm (refs : Refs ctx width) : CShape.Value .bit → Circuit model ctx ctx
  | .bit true => secondStepInto refs
  | .bit false => firstStepInto refs

/-- Actual selected pair store and path. -/
def nonDoneArmStep (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (nonDoneArm refs flag).Path :=
  match flag with
  | .bit true => secondStep refs store
  | .bit false => firstStep refs store

/-- A nonterminal iteration selects a pair using the actual stored phase. -/
def nonDoneStepInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .branch (phaseInput refs.machine.secondPhase) (nonDoneArm refs)

/-- Actual phase observation and selected pair execution. -/
def nonDoneStep (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (nonDoneStepInto refs).Path :=
  let flag := store.read (phaseInput refs.machine.secondPhase)
  let selected := nonDoneArmStep refs flag store
  (selected.1, ⟨flag, selected.2⟩)

/-- The actual terminal bit chooses identity or the original nonterminal driver. -/
def stepArm (refs : Refs ctx width) : CShape.Value .bit → Circuit model ctx ctx
  | .bit true => .id ctx
  | .bit false => nonDoneStepInto refs

/-- Actual selected terminal or nonterminal store and path. -/
def stepArmStep (refs : Refs ctx width) (flag : CShape.Value .bit) (store : Store ctx) :
    Store ctx × (stepArm refs flag).Path :=
  match flag with
  | .bit true => (store, ())
  | .bit false => nonDoneStep refs store

/-- One actual iteration reads the terminal bit before the pair-selection bit. -/
def stepInto (refs : Refs ctx width) : Circuit model ctx ctx :=
  .branch (phaseInput refs.machine.done) (stepArm refs)

/-- Both actual driver decisions are retained together with the selected instruction path. -/
def step (refs : Refs ctx width) (store : Store ctx) : Store ctx × (stepInto refs).Path :=
  let flag := store.read (phaseInput refs.machine.done)
  let selected := stepArmStep refs flag store
  (selected.1, ⟨flag, selected.2⟩)

/-- Fixed-fuel iteration of the actual classical-conditional circuit. -/
def fixedFuelInto (fuel : Nat) (refs : Refs ctx width) : Circuit model ctx ctx :=
  .iterate fuel (stepInto refs)

/-- Actual final store and all chronological iteration paths. -/
def fixedFuelStep (fuel : Nat) (refs : Refs ctx width) (store : Store ctx) :
    Store ctx × (fixedFuelInto fuel refs).Path :=
  ((fun current => (step refs current).1)^[fuel] store,
    fun index => (step refs ((fun current => (step refs current).1)^[index.val] store)).2)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
