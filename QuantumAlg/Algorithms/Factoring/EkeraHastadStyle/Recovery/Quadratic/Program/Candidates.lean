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

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width resultWidth : Nat}

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
theorem nativeQuadratic_candidateBody_execute (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (LocalLayout.candidateContext ctx width) Reference History) :
    (candidateBody input modulus original).execute Reference state =
      state.mapClassical (fun entry => ((candidateBodyStep input modulus original entry.1).1,
        (entry.2, (candidateBodyStep input modulus original entry.1).2))) := by
  let initialization := Initialized.code (LocalLayout.arithmeticRead input width)
    (LocalLayout.arithmeticRead modulus width) (LocalLayout.arithmeticRefs ctx width)
  let initializeStep := Initialized.step (LocalLayout.arithmeticRead input width)
    (LocalLayout.arithmeticRead modulus width) (LocalLayout.arithmeticRefs ctx width)
  let checks := CheckLayout.scopes (LocalLayout.candidateContext ctx width)
    (RSA.quadraticWordWidth width) (checkedBody modulus original)
  let checkStep := CheckLayout.scopeStep (RSA.quadraticWordWidth width)
    (checkedBody modulus original) (checkedBodyStep modulus original)
  refine (Circuit.execute_seq_mapClassical initialization checks initializeStep checkStep
    (Initialized.nativeQuadratic_initialized_execute (LocalLayout.arithmeticRead input width)
      (LocalLayout.arithmeticRead modulus width) (LocalLayout.arithmeticRefs ctx width))
    (CheckLayout.nativeQuadratic_checkScopes_execute (RSA.quadraticWordWidth width)
      (checkedBody modulus original) (checkedBodyStep modulus original)
      (nativeQuadratic_checkedBody_execute modulus original)) Reference state).trans ?_
  dsimp only [candidateBodyStep]
  refine (Circuit.mapClassical_canonicalDecision
    (C := Store (LocalLayout.candidateContext ctx width) × History)
    (D := Store (LocalLayout.candidateContext ctx width) ×
      (History × (candidateBody input modulus original).Path))
    (R := Register.prod (LocalLayout.candidateContext ctx width).register Reference)
    _ state _).trans ?_
  exact (Circuit.mapClassical_canonicalDecision
    (C := Store (LocalLayout.candidateContext ctx width) × History)
    (D := Store (LocalLayout.candidateContext ctx width) ×
      (History × (candidateBody input modulus original).Path))
    (R := Register.prod (LocalLayout.candidateContext ctx width).register Reference)
    _ state _).symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
