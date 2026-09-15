/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Parameters
import all QuantumAlg.Components.Classical.FirstAccepted.Option
import all QuantumAlg.Components.Classical.FirstAccepted.Resources
import all QuantumAlg.Components.Classical.FirstAccepted.Preservation

/-!
# Actual early-factor selection from retained sampler parameters

The parameter's structural tag and payload feed the canonical first-accepted
circuit. Its actual store updates retain a previous success and preserve every
caller read outside the four selector writes, including aliased scratch cells.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.RecoveryMachine

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Structural read of the early-factor tag in one retained parameter. -/
def earlyFactorTag (parameter : CInputRef ctx (ParameterShape N)) : CInputRef ctx .bit :=
  .first (.second parameter)

/-- Structural read of the early-factor payload in one retained parameter. -/
def earlyFactorPayload (parameter : CInputRef ctx (ParameterShape N)) :
    CInputRef ctx (.unsignedWord (modulusBits N)) := .second (.second parameter)

/-- Decode the existing tag and payload without allocating another cell. -/
def earlyFactorOption (parameter : CInputRef ctx (ParameterShape N))
    (store : Store ctx) : Option Nat :=
  if (store.read (earlyFactorTag parameter)).toBool then
    some (store.read (earlyFactorPayload parameter)).toNat else none

/-- A retained actual parameter carries exactly the sampler's optional early factor. -/
theorem earlyFactorOption_of_parameter (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (parameter : CInputRef ctx (ParameterShape N)) (store : Store ctx)
    (stored : store.read parameter = parameterValue input sample) :
    earlyFactorOption parameter store = (preparedResidue sample).earlyFactor := by
  unfold earlyFactorOption
  change (if (store.read parameter).second.first.toBool then
    some (store.read parameter).second.second.toNat else none) = _
  rw [stored]
  cases early : (preparedResidue sample).earlyFactor with
  | none =>
      have encoded := ShorStyle.Canonical.parameterValue_earlyFactor_none
        input.samplerInput sample (by
          simpa only [preparedResidue, modulusBits, residueProposalCount,
            ShorStyle.Canonical.modulusBits, ShorStyle.Canonical.residueProposalCount] using early)
      change (if (ShorStyle.Canonical.parameterValue input.samplerInput sample).second.first.toBool
        then some (ShorStyle.Canonical.parameterValue input.samplerInput sample).second.second.toNat
        else none) = none
      rw [encoded]
      rfl
  | some factor =>
      have encoded := ShorStyle.Canonical.parameterValue_earlyFactor_some
        input.samplerInput sample (by
          simpa only [preparedResidue, modulusBits, residueProposalCount,
            ShorStyle.Canonical.modulusBits, ShorStyle.Canonical.residueProposalCount] using early)
      change (if (ShorStyle.Canonical.parameterValue input.samplerInput sample).second.first.toBool
        then some (ShorStyle.Canonical.parameterValue input.samplerInput sample).second.second.toNat
        else none) = some factor
      rw [encoded.1, encoded.2]
      rfl

/-- The canonical selector reads the two existing parameter projections. -/
def earlyFactorInputs (parameter : CInputRef ctx (ParameterShape N)) :
    FirstAccepted.Inputs ctx (modulusBits N) where
  eligible := earlyFactorTag parameter
  candidate := earlyFactorPayload parameter

/-- The actual circuit uses the same four persistent and scratch references. -/
def earlyFactorSelector (parameter : CInputRef ctx (ParameterShape N))
    (refs : FirstAccepted.Refs ctx (modulusBits N)) : Circuit ctx ctx :=
  FirstAccepted.circuit (earlyFactorInputs parameter) refs

/-- Complete actual store and path of the early-factor selection. -/
def earlyFactorStep (parameter : CInputRef ctx (ParameterShape N))
    (refs : FirstAccepted.Refs ctx (modulusBits N)) (store : Store ctx) :
    Store ctx × (earlyFactorSelector parameter refs).Path :=
  FirstAccepted.step (earlyFactorInputs parameter) refs store

/-- Execution preserves incoming history and the complete external-reference record. -/
theorem earlyFactorSelector_execute (parameter : CInputRef ctx (ParameterShape N))
    (refs : FirstAccepted.Refs ctx (modulusBits N)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (earlyFactorSelector parameter refs).execute Reference state =
      state.mapClassical (fun entry => ((earlyFactorStep parameter refs entry.1).1,
        (entry.2, (earlyFactorStep parameter refs entry.1).2))) :=
  FirstAccepted.firstAccepted_execute _ _ _ _

/-- The actual output is the chronological retain-first update of the optional factor. -/
theorem earlyFactorSelector_selected (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N))
    (parameter : CInputRef ctx (ParameterShape N))
    (refs : FirstAccepted.Refs ctx (modulusBits N))
    (separation : FirstAccepted.Separated (earlyFactorInputs parameter) refs)
    (store : Store ctx) (stored : store.read parameter = parameterValue input sample) :
    (FirstAccepted.selectedOption refs (earlyFactorStep parameter refs store).1).map
        CShape.Value.toNat =
      FirstAccepted.retainFirst
        ((FirstAccepted.selectedOption refs store).map CShape.Value.toNat)
        (preparedResidue sample).earlyFactor := by
  have update := congrArg (Option.map CShape.Value.toNat)
    (FirstAccepted.firstAccepted_selectedOption (earlyFactorInputs parameter) refs separation store)
  have candidate : (FirstAccepted.candidateOption (earlyFactorInputs parameter) store).map
      CShape.Value.toNat = earlyFactorOption parameter store := by
    unfold FirstAccepted.candidateOption earlyFactorInputs earlyFactorOption
    split <;> rfl
  have mapped {α β : Type} (convert : α → β) (previous current : Option α) :
      (FirstAccepted.retainFirst previous current).map convert =
        FirstAccepted.retainFirst (previous.map convert) (current.map convert) := by
    cases previous <;> rfl
  rw [mapped, candidate,
    earlyFactorOption_of_parameter input sample parameter store stored] at update
  exact update

/-- Arbitrary caller reads outside all four actual writes remain unchanged. -/
theorem earlyFactorSelector_callerFrame (parameter : CInputRef ctx (ParameterShape N))
    (refs : FirstAccepted.Refs ctx (modulusBits N)) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (available : refs.available.key ∉ other.storageKeys)
    (take : refs.take.key ∉ other.storageKeys)
    (accepted : refs.accepted.key ∉ other.storageKeys)
    (selected : refs.selected.key ∉ other.storageKeys) :
    (earlyFactorStep parameter refs store).1.read other = store.read other :=
  FirstAccepted.firstAccepted_read_other _ _ _ available take accepted selected store

/-- Every actual native path obeys the independent four-operation selector allowance. -/
theorem earlyFactorSelector_pool_le (parameter : CInputRef ctx (ParameterShape N))
    (refs : FirstAccepted.Refs ctx (modulusBits N))
    (path : (earlyFactorSelector parameter refs).Path) :
    (earlyFactorSelector parameter refs).resourcePool path ≤
      FirstAccepted.nativeEnvelope kind (modulusBits N) :=
  FirstAccepted.firstAccepted_pool_le _ _ path

/-- Resident storage retains the full actual caller context on every path. -/
theorem earlyFactorSelector_resident_le (parameter : CInputRef ctx (ParameterShape N))
    (refs : FirstAccepted.Refs ctx (modulusBits N))
    (path : (earlyFactorSelector parameter refs).Path) :
    (earlyFactorSelector parameter refs).peakResidentSpace path ≤ ctx.residentSpace :=
  FirstAccepted.firstAccepted_resident_le _ _ path

/-- Auxiliary storage includes the existing caller workspace roles on every path. -/
theorem earlyFactorSelector_auxiliary_le (parameter : CInputRef ctx (ParameterShape N))
    (refs : FirstAccepted.Refs ctx (modulusBits N))
    (path : (earlyFactorSelector parameter refs).Path) :
    (earlyFactorSelector parameter refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace :=
  FirstAccepted.firstAccepted_auxiliary_le _ _ path

/-- Borrowed storage is restored jointly with an arbitrary external quantum reference. -/
theorem earlyFactorSelector_borrowedRestored (parameter : CInputRef ctx (ParameterShape N))
    (refs : FirstAccepted.Refs ctx (modulusBits N)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (earlyFactorSelector parameter refs).BorrowedRestored Reference state
      ((earlyFactorSelector parameter refs).execute Reference state) :=
  FirstAccepted.firstAccepted_borrowedRestored _ _ _ _

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.RecoveryMachine
