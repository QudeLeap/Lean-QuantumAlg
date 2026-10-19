/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Program.Checked
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Check.Scope
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# Complete execution of initialized candidates and actual scoped checks

The candidate instructions and actual one loading run before the five real
checker allocations. Their complete execution is followed by both checks,
local selection, narrowing and persistent result update, then reverse release
of the checker cells. The true chronological path and all incoming joint
quantum-reference blocks remain in the same native execution equation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel}
    {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {width resultWidth : Nat}

/-- Actual candidate initialization and checker scopes return their recorded stores and paths. -/
def candidateBodyStep (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth)
    (store : Store (LocalLayout.candidateContext ctx width)) :
    Store (LocalLayout.candidateContext ctx width) × (candidateBody input modulus original).Path :=
  let initialized := Initialized.step (LocalLayout.arithmeticRead input width)
    (LocalLayout.arithmeticRead modulus width) (LocalLayout.arithmeticRefs ctx width) store
  let checked := CheckLayout.scopeStep (RSA.quadraticWordWidth width)
    (checkedBody modulus original) (checkedBodyStep modulus original) initialized.1
  (checked.1, (initialized.2, checked.2))

/-- The actual initialized and scoped body preserves every complete incoming matrix block. -/
lemma nativeQuadratic_candidateBody_execute (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (LocalLayout.candidateContext ctx width) Reference
      (model.HiddenState × History)) :
    (candidateBody input modulus original).execute environment Reference state =
      state.mapClassical (fun entry => ((candidateBodyStep input modulus original entry.1).1,
        (entry.2.1, (entry.2.2, (candidateBodyStep input modulus original entry.1).2)))) := by
  have checksLaw (reference : Register) {history : Type} [Fintype history]
      (initial : State (LocalLayout.candidateContext ctx width) reference
        (model.HiddenState × history)) :
      (CheckLayout.scopes (LocalLayout.candidateContext ctx width)
        (RSA.quadraticWordWidth width) (checkedBody modulus original)).execute environment
          reference initial =
      initial.mapClassical (fun entry =>
        let actual := CheckLayout.scopeStep (RSA.quadraticWordWidth width)
          (checkedBody modulus original) (checkedBodyStep modulus original) entry.1
        (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
    CheckLayout.nativeQuadratic_checkScopes_execute (RSA.quadraticWordWidth width)
      (checkedBody modulus original) (checkedBodyStep modulus original)
      (nativeQuadratic_checkedBody_execute modulus original) reference initial
  simp only [candidateBody, Circuit.execute_seq, Initialized.nativeQuadratic_initialized_execute,
    checksLaw, State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
