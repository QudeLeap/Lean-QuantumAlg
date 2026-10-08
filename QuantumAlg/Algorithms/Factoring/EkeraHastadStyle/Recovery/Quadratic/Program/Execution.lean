/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Program.Candidates
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Layout.Execution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Selection.Execution

/-!
# Complete actual scoped quadratic execution

The complete program executes the actual initialization, both divisor checks,
local selection, width conversion and persistent selector. All thirteen
classical workspace cells are released by their actual enclosing scopes.
The interpreter equation records the real chronological path and preserves
each complete incoming quantum-reference block without an initialization
or quantum-absence premise.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {width resultWidth : Nat}

/-- The actual eight outer scopes retain the already recorded candidate and checking path. -/
def programStep (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (store : Store ctx) :
    Store ctx × (program input modulus original).Path :=
  SelectionLayout.scopeStep (RSA.quadraticWordWidth width)
    (Layout.scopes (LocalLayout.selectionContext ctx width) width
      (candidateBody input modulus original))
    (Layout.scopeStep width (candidateBody input modulus original)
      (candidateBodyStep input modulus original)) store

/-- Complete execution is the same actual scoped store update, including its true path. -/
theorem nativeQuadratic_program_execute (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (program input modulus original).execute Reference state =
      state.mapClassical (fun entry => ((programStep input modulus original entry.1).1,
        (entry.2.1, (entry.2.2, (programStep input modulus original entry.1).2)))) :=
  SelectionLayout.nativeRecovery_selectionScopes_execute (RSA.quadraticWordWidth width)
    (Layout.scopes (LocalLayout.selectionContext ctx width) width
      (candidateBody input modulus original))
    (Layout.scopeStep width (candidateBody input modulus original)
      (candidateBodyStep input modulus original))
    (Layout.nativeQuadratic_layoutScopes_execute width (candidateBody input modulus original)
      (candidateBodyStep input modulus original)
      (nativeQuadratic_candidateBody_execute input modulus original)) Reference state

set_option maxHeartbeats 800000 in -- Align store projections through eight actual lexical scopes.
/-- Scope release exposes the surviving original store after the actual candidate body. -/
theorem nativeQuadratic_programStep_store (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (store : Store ctx) :
    (programStep input modulus original store).1 =
      SelectionLayout.popStore (RSA.quadraticWordWidth width)
        (Layout.popStore width (candidateBodyStep input modulus original
          (Layout.pushStore width
            (SelectionLayout.pushStore (RSA.quadraticWordWidth width) store))).1) := by
  let inner := candidateBody (model := model) input modulus original
  let update := candidateBodyStep (model := model) input modulus original
  have outer := SelectionLayout.nativeRecovery_selectionScopeStep_store
    (RSA.quadraticWordWidth width)
    (Layout.scopes (LocalLayout.selectionContext ctx width) width inner)
    (Layout.scopeStep width inner update) store
  have inside := Layout.nativeQuadratic_layoutScopeStep_store width inner update
    (SelectionLayout.pushStore (RSA.quadraticWordWidth width) store)
  exact outer.trans (congrArg (SelectionLayout.popStore (RSA.quadraticWordWidth width)) inside)

set_option maxHeartbeats 800000 in -- Match original read positions across the same eight scopes.
/-- Every surviving original read is exactly the corresponding read before outer scope release. -/
theorem nativeQuadratic_programStep_read (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) {shape : CShape}
    (other : CInputRef ctx shape) (store : Store ctx) :
    (programStep input modulus original store).1.read other =
      (candidateBodyStep input modulus original (Layout.pushStore width
        (SelectionLayout.pushStore (RSA.quadraticWordWidth width) store))).1.read
        (LocalLayout.arithmeticRead other width) :=
  (congrArg (fun final : Store ctx => final.read other)
    (nativeQuadratic_programStep_store input modulus original store)).trans
    ((SelectionLayout.nativeRecovery_selection_pop_read other (RSA.quadraticWordWidth width)
      _).trans (Layout.nativeQuadratic_layout_pop_read
        (SelectionLayout.underRead other (RSA.quadraticWordWidth width)) width _))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
