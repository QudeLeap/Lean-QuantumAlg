/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Selection
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Frame
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scan.Execution
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Frame
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Scope.Records
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.Selector
import all QuantumAlg.Algorithms.Factoring.ShorStyle.FactorRecovery.SamplingInput
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Parameters
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Outcome

/-!
# The actual finite scan returns the original first successful source factor

The proof reads each actual parameter and phase pair from its retained cells,
runs native order recovery and the original priority factor selector, and
uses the existing latch circuit. The internal key facts below are discharged
by the concrete four-head scope. No semantic result is written by a callback,
and neither the initial latch nor the selected payload is a caller premise.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan

open Execution ClassicalRoutines

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Original mathematical factor recovery for the same source sample and Born outcome. -/
def sourceResult (source : Input N) (outcome : SourceOutcome N) :
    CShape.Value (.option (.unsignedWord (modulusBits N))) :=
  FactorRecovery.encodeOutput (FactorRecovery.outputOfRecovered
    (parameterValue source outcome.sample)
    (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
      (FactorRecovery.recoverySpec source)
      (FactorRecovery.sampledSemanticInput source outcome.sample outcome.measurement)))

/-- The first present original source result in the actual input-reference order. -/
def sourceResults (source : Input N) : List (SourceOutcome N) →
    CShape.Value (.option (.unsignedWord (modulusBits N)))
  | [] => .optionNone
  | outcome :: rest => firstPresent (sourceResult source outcome) (sourceResults source rest)

/-- All persistent latch conditions used internally by a complete actual visit. -/
structure Separated (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N)))) : Prop where
  selector : FirstAccepted.Separated (selectorInputs cells) (selectorRefs cells)
  candidateAccepted : cells.candidate.key ≠ cells.accepted.key
  candidateSelected : cells.candidate.key ≠ cells.selected.key
  resultAccepted : result.key ≠ cells.accepted.key
  resultSelected : result.key ≠ cells.selected.key

private theorem firstPresent_none_right {width : Nat}
    (value : CShape.Value (.option (.unsignedWord width))) :
    firstPresent value .optionNone = value := by
  cases value <;> rfl

private theorem firstPresent_assoc {width : Nat}
    (first second third : CShape.Value (.option (.unsignedWord width))) :
    firstPresent (firstPresent first second) third =
      firstPresent first (firstPresent second third) := by
  cases first <;> rfl

/-- The internal actual-read facts used to identify each retained source outcome. -/
def Represents (source : Input N) (entries : List (Inputs ctx N × SourceOutcome N))
    (store : Store ctx) : Prop :=
  ∀ entry ∈ entries,
    store.read entry.1.parameter = parameterValue source entry.2.sample ∧
      store.read entry.1.phase = .bits entry.2.measurement

/-- Every original retained operand avoids the actual scan's surviving writes. -/
def Frames (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (entries : List (Inputs ctx N × SourceOutcome N)) : Prop :=
  ∀ entry ∈ entries,
    FrameFree cells result entry.1.parameter ∧ FrameFree cells result entry.1.phase

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Actual factor recovery and selection preserve the first successful factor exactly. -/
theorem visit_latchValue (source : Input N) (inputs : Inputs ctx N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : Separated cells result) (store : Store ctx) (outcome : SourceOutcome N)
    (parameterRead : store.read inputs.parameter = parameterValue source outcome.sample)
    (phaseRead : store.read inputs.phase = .bits outcome.measurement) :
    latchValue cells (visitStep (model := model) source inputs cells result store).1 =
      firstPresent (latchValue cells store) (sourceResult source outcome) := by
  let semantic := FactorRecovery.sampledSemanticInput source outcome.sample outcome.measurement
  let recovered := FactorRecovery.NativeFactorScope.step (model := model) source
    inputs.parameter inputs.phase result store
  have baseRead : (store.read inputs.parameter).first.toNat = semantic.base.val :=
    (congrArg (fun value => value.first.toNat) parameterRead).trans
      (parameterValue_unit_toNat source outcome.sample)
  have actualResult : recovered.1.read (.storage result.toCStorageRef) =
      sourceResult source outcome :=
    (FactorRecovery.NativeFactorScope.result (model := model) source semantic inputs.parameter
      inputs.phase
      result store baseRead phaseRead).trans
      (congrArg (fun parameter => FactorRecovery.encodeOutput
        (FactorRecovery.outputOfRecovered parameter
          (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
            (FactorRecovery.recoverySpec source) semantic))) parameterRead)
  have acceptedSame := FactorRecovery.NativeFactorScope.read_other (model := model) source
    inputs.parameter inputs.phase result (.storage cells.accepted.toCStorageRef)
    (fun member => separated.resultAccepted (List.mem_singleton.mp member)) store
  have selectedSame := FactorRecovery.NativeFactorScope.read_other (model := model) source
    inputs.parameter inputs.phase result (.storage cells.selected.toCStorageRef)
    (fun member => separated.resultSelected (List.mem_singleton.mp member)) store
  have latchesSame : latchValue cells recovered.1 = latchValue cells store :=
    congrArg CShape.packOption (congrArg₂ CShape.Value.product acceptedSame selectedSame)
  exact (selection_latchValue (model := model) cells result separated.selector
    separated.candidateAccepted
    separated.candidateSelected recovered.1).trans
    (congrArg₂ firstPresent latchesSame actualResult)

/-- Actual scanning folds the source selector while retaining an earlier accepted result. -/
theorem scan_latchValue (source : Input N) (cells : Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : Separated cells result) (entries : List (Inputs ctx N × SourceOutcome N)) :
    ∀ (store : Store ctx), Frames cells result entries → Represents source entries store →
      latchValue cells (scanStep (model := model) source cells result (entries.map Prod.fst)
        store).1 =
        firstPresent (latchValue cells store) (sourceResults source (entries.map Prod.snd)) := by
  induction entries with
  | nil =>
      intro store _ _
      exact (firstPresent_none_right (latchValue cells store)).symm
  | cons entry rest ih =>
      intro store frames represented
      let visited := visitStep (model := model) source entry.1 cells result store
      have current := represented entry List.mem_cons_self
      have laterFrames : Frames cells result rest :=
        fun later member => frames later (List.mem_cons_of_mem entry member)
      have laterReads : Represents source rest visited.1 := by
        intro later member
        have original := represented later (List.mem_cons_of_mem entry member)
        have free := laterFrames later member
        have parameterSame := visit_read_other (model := model) source entry.1 cells result
          later.1.parameter free.1 store
        have phaseSame := visit_read_other (model := model) source entry.1 cells result
          later.1.phase free.2 store
        exact ⟨parameterSame.trans original.1, phaseSame.trans original.2⟩
      have remaining := ih visited.1 laterFrames laterReads
      have currentResult := visit_latchValue (model := model) source entry.1 cells result separated
        store entry.2 current.1 current.2
      refine remaining.trans ?_
      exact (congrArg (fun value =>
        firstPresent value (sourceResults source (rest.map Prod.snd))) currentResult).trans
        (firstPresent_assoc _ _ _)

/-- The actual initialized scan writes exactly the first successful original source result. -/
theorem code_result (source : Input N) (entries : List (Inputs ctx N × SourceOutcome N))
    (cells : Cells ctx N) (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : Separated cells result) (store : Store ctx)
    (frames : Frames cells result entries) (represented : Represents source entries store) :
    (step (model := model) source (entries.map Prod.fst) cells result store).1.read
      (.storage result.toCStorageRef) = sourceResults source (entries.map Prod.snd) := by
  let cleared := store.applyOp (clearAcceptedOp cells)
  have clearedReads : Represents source entries cleared := by
    intro entry member
    have original := represented entry member
    have free := frames entry member
    exact ⟨(Store.read_applyOp_of_not_mem_storageKeys store (clearAcceptedOp cells)
        entry.1.parameter free.1.accepted).trans original.1,
      (Store.read_applyOp_of_not_mem_storageKeys store (clearAcceptedOp cells)
        entry.1.phase free.2.accepted).trans original.2⟩
  refine (pack_result cells result
    (scanStep (model := model) source cells result (entries.map Prod.fst) cleared).1).trans
    ((scan_latchValue (model := model) source cells result separated entries cleared frames
      clearedReads).trans ?_)
  rw [clear_latchValue]
  rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeFactorScan
