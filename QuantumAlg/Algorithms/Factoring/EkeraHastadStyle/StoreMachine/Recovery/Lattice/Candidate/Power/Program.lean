/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Program.Layout

/-!
# Actual candidate modular power and target comparison
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePowerMachine

open Execution
open ClassicalAlgorithms.Modular
open ClassicalRoutines.Modular.NativePower

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width exponentWidth : Nat}

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The shared actual modular-power circuit owns its real lexical scratch and initialization. -/
def powerInto (spec : ModulusSpec width) (refs : Refs ctx width exponentWidth) :
    Circuit model ctx ctx :=
  into (model := model) spec refs.generator refs.exponent refs.power

/-- The actual initialized modular fold's complete returned store and selected branch history. -/
def powerStep (spec : ModulusSpec width) (refs : Refs ctx width exponentWidth) (store : Store ctx) :
    Store ctx × (powerInto spec refs).Path :=
  intoStep spec refs.generator refs.exponent refs.power store

/-- Actual equality reads the computed raw power and the original supplied target. -/
def equalityOp (refs : Refs ctx width exponentWidth) :
    ClassicalOp (.product (.unsignedWord width) (.unsignedWord width)) .bit ctx ctx :=
  .wordBinary .equal width ctx (.product (writeInput refs.power) refs.targetPower) refs.accepted

/-- Execute actual initialized modular powering followed by the original target test. -/
def candidatePowerInto (spec : ModulusSpec width) (refs : Refs ctx width exponentWidth) :
    Circuit model ctx ctx :=
  .seq (powerInto spec refs) (BitWord.instruction (execution := model) (equalityOp refs))

/-- The complete actual power store followed by the actual stored comparison result. -/
def candidateStep (spec : ModulusSpec width) (refs : Refs ctx width exponentWidth)
    (store : Store ctx) : Store ctx × (candidatePowerInto spec refs).Path :=
  let powered := powerStep spec refs store
  let compared := BitWord.instructionStep (execution := model) (equalityOp refs) powered.1
  (compared.1, (powered.2, compared.2))

/-- The full actual interpreter includes all native power branches and the final equality. -/
theorem candidatePowerInto_execute (spec : ModulusSpec width)
    (refs : Refs ctx width exponentWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (candidatePowerInto spec refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := candidateStep spec refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) := by
  refine (Circuit.execute_seq_mapClassical (powerInto spec refs)
    (BitWord.instruction (execution := model) (equalityOp refs))
    (fun before =>
      let actual := powerStep spec refs before.1
      ((actual.1, before.2), actual.2))
    (fun before =>
      let actual := BitWord.instructionStep (execution := model) (equalityOp refs) before.1
      ((actual.1, before.2), actual.2))
    (fun reference _history _ current =>
      nativePower_into_execute spec refs.generator refs.exponent refs.power reference current)
    (fun reference _history _ current => BitWord.bitWord_instruction_execute _ current)
    Reference state).trans ?_
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeCandidatePowerMachine
