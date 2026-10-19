/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Semantics
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Actual narrowing before persistent first-factor selection

A single real lexical word receives the width conversion of a checked wide
candidate. The existing first-accepted circuit then consumes that word and
the actual eligibility bit. Earlier persistent factors therefore remain
unchanged even if the candidate's width differs. The same lexical word is
released after selection. Representability of accepted factors is proved at
the source boundary; the actual resize itself is defined at every width.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.NarrowSelection

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {sourceWidth width : Nat}

/-- One actual fresh word holds the resized candidate before persistent selection. -/
def context (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- The resized candidate is written only to the actual new lexical head. -/
def temporary (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (context ctx width) (.unsignedWord width) :=
  .workspaceHead ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- Original input references pass unchanged beneath the actual new word. -/
def underRead {shape : CShape} (input : CInputRef ctx shape) (width : Nat) :
    CInputRef (context ctx width) shape :=
  input.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- Original selector destinations remain their real writable cells beneath the lexical word. -/
def underWrite {shape : CShape} (output : CWriteRef ctx shape) (width : Nat) :
    CWriteRef (context ctx width) shape :=
  output.underWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh

/-- Genuine native width conversion writes the temporary word before its possible selection. -/
def resizeOp (candidate : CInputRef ctx (.unsignedWord sourceWidth)) (width : Nat) :
    ClassicalOp (.unsignedWord sourceWidth) (.unsignedWord width)
      (context ctx width) (context ctx width) :=
  .wordResize sourceWidth width (context ctx width)
    (underRead candidate width) (temporary ctx width)

/-- The selector consumes the actual stored eligibility and the actual converted candidate word. -/
def inputs (eligible : CInputRef ctx .bit) (width : Nat) :
    FirstAccepted.Inputs (context ctx width) width where
  eligible := underRead eligible width
  candidate := .storage (temporary ctx width).toCStorageRef

/-- The same persistent latches and real scratch bits receive the selector's writes. -/
def refs (original : FirstAccepted.Refs ctx width) :
    FirstAccepted.Refs (context ctx width) width where
  accepted := underWrite original.accepted width
  selected := underWrite original.selected width
  available := underWrite original.available width
  take := underWrite original.take width

noncomputable section

variable {model : ExecutionModel} {environment : model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Actual conversion followed by existing native first-accepted selection. -/
def body (eligible : CInputRef ctx .bit) (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width) :
    Circuit model (context ctx width) (context ctx width) :=
  .seq (BitWord.instruction (resizeOp candidate width))
    (FirstAccepted.circuit (inputs eligible width) (refs original))

/-- The actual conversion word is allocated and released around the same real selector call. -/
def code (eligible : CInputRef ctx .bit) (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    (body eligible candidate original)

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Actual conversion and selection stores with both real instruction and branch paths. -/
def bodyStep (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width)
    (store : Store (context ctx width)) :
    Store (context ctx width) × (body eligible candidate original).Path :=
  let resized := BitWord.instructionStep (execution := model) (resizeOp candidate width) store
  let selected := FirstAccepted.step (model := model) (inputs eligible width) (refs original)
    resized.1
  (selected.1, (resized.2, selected.2))

/-- The real one-word scope encloses precisely the recorded conversion and selection update. -/
def step (eligible : CInputRef ctx .bit) (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width) (store : Store ctx) :
    Store ctx × (code eligible candidate original).Path :=
  let selected := bodyStep eligible candidate original
    (store.pushWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh
    selected.1, selected.2)

/-- Actual body execution preserves all complete incoming quantum-reference matrix blocks. -/
lemma nativeQuadratic_narrow_body_execute (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx width) Reference (model.HiddenState × History)) :
    (body eligible candidate original).execute environment
      Reference state = state.mapClassical (fun entry =>
      ((bodyStep eligible candidate original entry.1).1,
        (entry.2.1, (entry.2.2, (bodyStep eligible candidate original entry.1).2)))) := by
  simp only [body, Circuit.execute_seq, BitWord.bitWord_instruction_execute,
    FirstAccepted.firstAccepted_execute, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

/-- Scope entry and release retain the complete original quantum-reference correlations. -/
lemma nativeQuadratic_narrow_execute (eligible : CInputRef ctx .bit)
    (candidate : CInputRef ctx (.unsignedWord sourceWidth))
    (original : FirstAccepted.Refs ctx width)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (code eligible candidate original).execute environment
      Reference state = state.mapClassical (fun entry =>
      ((step eligible candidate original entry.1).1,
        (entry.2.1, (entry.2.2, (step eligible candidate original entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical
    (environment := environment) ctx.canonicalFreshKey (.unsignedWord width)
    ctx.canonicalFreshKey_fresh (body eligible candidate original)
    (fun before =>
      let actual := bodyStep eligible candidate original before.1
      ((actual.1, before.2), actual.2))
    (fun reference {_} _ initial =>
      nativeQuadratic_narrow_body_execute eligible candidate original reference initial)
    Reference state).trans ?_
  congr 1

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic.NarrowSelection
