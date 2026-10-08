/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Util.RSA.ShortLog.Widths
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Selection.EarlyFactor
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Quadratic.Selection.Candidate.Layout
import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Execution.Trace.Bounds

/-!
# Actual widened early-factor seed

One real resize widens the retained parameter payload before the canonical
first-accepted selector reads it. The same actual stores determine the full
output and caller frame; each possible native path contains at most five operations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeEarlyFactorSeed

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Width shared by the persistent factor selector and pair recovery. -/
abbrev Width (N : Nat) : Nat :=
  QuadraticCandidateCheck.CandidateWidth (LatticePairCandidateRecovery.Width N)

/-- The modulus-sized early-factor payload fits the pair selector width. -/
theorem modulusBits_le_width (N : Nat) : modulusBits N ≤ Width N := by
  have modulusBitsLeSize : modulusBits N ≤ Nat.size N :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_size_self N))
  have sizeLeInput : Nat.size N ≤
      RSA.shortLogRecoveryInputBits N (shortLogBits N) (tradeoffBits N) := by
    simp only [RSA.shortLogRecoveryInputBits]
    omega
  have modulusBitsLeInput := modulusBitsLeSize.trans sizeLeInput
  simp only [Width,
    LatticePairCandidateRecovery.Width, LatticeWideLllMachine.Width,
    QuadraticCandidateCheck.CandidateWidth, QuadraticPrefix.centerWidth,
    RSA.ShortLogWidths.coordinateWidth, RSA.ShortLogWidths.operandWidthBound,
    RSA.ShortLogWidths.inputBitWidth]
  omega

/-- One real widening word and the persistent canonical selector. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  wideCandidate : CWriteRef ctx (.unsignedWord (Width N))
  selection : FirstAccepted.Refs ctx (Width N)

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- The selector reads the original tag and the actual widened payload. -/
def selectionInputs {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N) :
    FirstAccepted.Inputs ctx (Width N) where
  eligible := RecoveryMachine.earlyFactorTag parameter
  candidate := FirstAccepted.cellRead refs.wideCandidate

/-- The original independent frame and selector separation conditions. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N) : Prop where
  tagAvoidsWide : refs.wideCandidate.key ∉ (RecoveryMachine.earlyFactorTag parameter).storageKeys
  payloadAvoidsWide :
    refs.wideCandidate.key ∉ (RecoveryMachine.earlyFactorPayload parameter).storageKeys
  acceptedAvoidsWide :
    refs.wideCandidate.key ∉ (FirstAccepted.cellRead refs.selection.accepted).storageKeys
  selectedAvoidsWide :
    refs.wideCandidate.key ∉ (FirstAccepted.cellRead refs.selection.selected).storageKeys
  selection : FirstAccepted.Separated (selectionInputs parameter refs) refs.selection

/-- Every possible destination is excluded from the preserved caller read. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  wideCandidate : refs.wideCandidate.key ∉ other.storageKeys
  accepted : refs.selection.accepted.key ∉ other.storageKeys
  selected : refs.selection.selected.key ∉ other.storageKeys
  available : refs.selection.available.key ∉ other.storageKeys
  take : refs.selection.take.key ∉ other.storageKeys

/-- The single actual word resize from public modulus width to recovery width. -/
def resizeOp {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N) :=
  ClassicalOp.wordResize (modulusBits N) (Width N) ctx
    (RecoveryMachine.earlyFactorPayload parameter) refs.wideCandidate

/-- Resize the payload, then run the existing first-accepted circuit on the actual store. -/
def into (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N) :
    Circuit model ctx ctx :=
  .seq (BitWord.instruction (execution := model) (resizeOp parameter refs))
    (FirstAccepted.circuit (selectionInputs parameter refs) refs.selection)

/-- Complete actual store and chronological path of both stages. -/
def step (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (into parameter refs).Path :=
  let resized := BitWord.instructionStep (execution := model) (resizeOp parameter refs) store
  let selected := FirstAccepted.step (selectionInputs parameter refs) refs.selection resized.1
  (selected.1, (resized.2, selected.2))

/-- Full actual execution preserves the incoming history and external-reference record. -/
theorem into_execute (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into parameter refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := step parameter refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  Circuit.execute_sequenceStoreRecord _ _ _ _
    (fun _reference _history _ current => BitWord.bitWord_instruction_execute _ current)
    (FirstAccepted.firstAccepted_execute (selectionInputs parameter refs) refs.selection)
    Reference state

/-- Every structurally disjoint caller read survives both actual writes and selector branches. -/
theorem into_callerFrame (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N)
    (store : Store ctx) {shape : CShape} (other : CInputRef ctx shape)
    (avoids : CallerFrameAvoids refs other) :
    (step parameter refs store).1.read other = store.read other :=
  (FirstAccepted.firstAccepted_read_other _ _ other avoids.available avoids.take
    avoids.accepted avoids.selected _).trans
    (Store.read_applyOp_of_not_mem_storageKeys store (resizeOp parameter refs) other
      avoids.wideCandidate)

/-- The optional early factor and every disjoint caller value belong to the same actual result. -/
structure Relation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (sample : Fin (2 ^ residueSamplingBits N)) (refs : Refs ctx N)
    (before after : Store ctx) : Prop where
  selected : QuadraticCandidateSelect.selectedOption refs.selection after =
    FirstAccepted.retainFirst (QuadraticCandidateSelect.selectedOption refs.selection before)
      (preparedResidue sample).earlyFactor
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- Actual widening and selection realize the parameter's retain-first update without truncation. -/
theorem into_correct (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N)
    (separation : Separation parameter refs) (store : Store ctx)
    (stored : store.read parameter = parameterValue input sample) :
    Relation sample refs store (step parameter refs store).1 := by
  let middle := store.applyOp (resizeOp parameter refs)
  have tagAt := Store.read_applyOp_of_not_mem_storageKeys store (resizeOp parameter refs)
    (RecoveryMachine.earlyFactorTag parameter) separation.tagAvoidsWide
  have acceptedAt := Store.read_applyOp_of_not_mem_storageKeys store (resizeOp parameter refs)
    (FirstAccepted.cellRead refs.selection.accepted) separation.acceptedAvoidsWide
  have selectedAt := Store.read_applyOp_of_not_mem_storageKeys store (resizeOp parameter refs)
    (FirstAccepted.cellRead refs.selection.selected) separation.selectedAvoidsWide
  have previous : QuadraticCandidateSelect.selectedOption refs.selection middle =
      QuadraticCandidateSelect.selectedOption refs.selection store := by
    unfold QuadraticCandidateSelect.selectedOption FirstAccepted.selectedOption
    rw [acceptedAt, selectedAt]
  have fits : (store.read (RecoveryMachine.earlyFactorPayload parameter)).toNat <
      CShape.wordModulus (Width N) :=
    (store.read (RecoveryMachine.earlyFactorPayload parameter)).toNat_lt.trans_le
      (Nat.pow_le_pow_right (by omega) (modulusBits_le_width N))
  have wide : (middle.read (FirstAccepted.cellRead refs.wideCandidate)).toNat =
      (store.read (RecoveryMachine.earlyFactorPayload parameter)).toNat := by
    have written := congrArg CShape.Value.toNat
      (Store.read_applyOp_output store (resizeOp parameter refs))
    exact written.trans (ClassicalOp.eval_wordResize_exact _ _ _ _ _ _ fits)
  have candidate : (FirstAccepted.candidateOption (selectionInputs parameter refs) middle).map
      CShape.Value.toNat = (preparedResidue sample).earlyFactor := by
    rw [← RecoveryMachine.earlyFactorOption_of_parameter input sample parameter store stored]
    unfold FirstAccepted.candidateOption selectionInputs RecoveryMachine.earlyFactorOption
    rw [tagAt]
    split <;> simp only [Option.map_some, Option.map_none, wide]
  have update := congrArg (Option.map CShape.Value.toNat)
    (FirstAccepted.firstAccepted_selectedOption (selectionInputs parameter refs)
      refs.selection separation.selection middle)
  have mapped {α β : Type} (convert : α → β) (previous current : Option α) :
      (FirstAccepted.retainFirst previous current).map convert =
        FirstAccepted.retainFirst (previous.map convert) (current.map convert) := by
    cases previous <;> rfl
  rw [mapped, candidate] at update
  change QuadraticCandidateSelect.selectedOption refs.selection
    (FirstAccepted.step (selectionInputs parameter refs) refs.selection middle).1 =
      FirstAccepted.retainFirst (QuadraticCandidateSelect.selectedOption refs.selection middle)
        (preparedResidue sample).earlyFactor at update
  rw [previous] at update
  exact ⟨update, into_callerFrame parameter refs store⟩

/-- Independent native envelope for the one resize and the four possible selector operations. -/
def eventEnvelope (N : Nat) : ResourcePool model :=
  ResourcePool.singleton (.classicalOperation (BitWord.selectedCoordinate (execution := model)
    (.wordResize (modulusBits N) (Width N)))) +
    FirstAccepted.nativeEnvelope model (Width N)

/-- Every actual path satisfies the independent sum of the resize and selector budgets. -/
theorem into_pool_le (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N)
    (path : (into parameter refs).Path) :
    (into parameter refs).resourcePool path ≤ eventEnvelope N := by
  change ResourcePool.ofList
    ((BitWord.instruction (execution := model) (resizeOp parameter refs)).eventTrace path.1 ++
    (FirstAccepted.circuit (selectionInputs parameter refs) refs.selection).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append, BitWord.bitWord_instruction_eventTrace]
  exact add_le_add (le_refl _) (FirstAccepted.firstAccepted_pool_le _ _ path.2)

/-- At most five unit-duration native dependencies occur on every actual path. -/
theorem into_depth_le (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N)
    (path : (into parameter refs).Path) :
    (into parameter refs).depth (fun _ => 1) path ≤ 5 := by
  change 1 + (FirstAccepted.circuit (selectionInputs parameter refs) refs.selection).depth
    (fun _ => 1) path.2 ≤ 5
  rw [FirstAccepted.firstAccepted_unit_depth]
  split <;> omega

/-- Every actual visited scope is the complete incoming context. -/
theorem into_visited (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N)
    (path : (into parameter refs).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (into parameter refs).visitedContexts path) : visited = ctx := by
  change visited ∈ [ctx] ++
    (FirstAccepted.circuit (selectionInputs parameter refs) refs.selection).visitedContexts path.2
    at present
  rcases List.mem_append.mp present with before | selected
  · exact List.mem_singleton.mp before
  · exact FirstAccepted.firstAccepted_visited _ _ _ _ selected

/-- The same actual run retains all incoming resident storage. -/
theorem into_resident_le (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N)
    (path : (into parameter refs).Path) :
    (into parameter refs).peakResidentSpace path ≤ ctx.residentSpace := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  rw [into_visited parameter refs path visited present]

/-- The same actual run includes all existing auxiliary workspace roles. -/
theorem into_auxiliary_le (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N)
    (path : (into parameter refs).Path) :
    (into parameter refs).peakAuxiliarySpace path ≤ ctx.auxiliarySpace := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  rw [into_visited parameter refs path visited present]

/-- Widening and selection restore the full borrowed interface jointly with any reference. -/
theorem into_borrowedRestored (parameter : CInputRef ctx (ParameterShape N)) (refs : Refs ctx N)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into parameter refs).BorrowedRestored Reference state
      ((into parameter refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (Circuit.borrowedRestored_classical
      (BitWord.selectedApplication (execution := model) (resizeOp parameter refs)) state)
    (FirstAccepted.firstAccepted_borrowedRestored _ _ _ _)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeEarlyFactorSeed
