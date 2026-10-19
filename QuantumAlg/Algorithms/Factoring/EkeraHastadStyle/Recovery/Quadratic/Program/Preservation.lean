/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Program
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Candidates.Preservation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Pair.Preservation
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection.Narrow.Preservation

/-!
# Complete borrowed restoration of actual scoped quadratic recovery

Every executed arithmetic instruction, complete divisor check and conditional
selection acts on its declared writable cells. The actual lexical pushes
and reverse pops enclose exactly those circuits. Composing their existing
restoration laws preserves the joint borrowed classical-quantum-reference
state, even when the incoming caller cells are correlated with that state.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open Execution
open ClassicalRoutines

variable {model : ExecutionModel}
    {environment : model.Environment} {ctx : RuntimeCtx model.kind} {width resultWidth : Nat}

private lemma check_scopes_restore (width : Nat)
    (inner : Circuit model (CheckLayout.context ctx width) (CheckLayout.context ctx width))
    (Reference : Register)
    (restores : ∀ {History : Type} [Fintype History]
      (state : State (CheckLayout.context ctx width) Reference (model.HiddenState × History)),
      inner.BorrowedRestored Reference state (inner.execute environment Reference state))
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (CheckLayout.scopes ctx width inner).BorrowedRestored Reference state
      ((CheckLayout.scopes ctx width inner).execute environment Reference state) := by
  unfold CheckLayout.scopes
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history0 finite0 entered0
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history1 finite1 entered1
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history2 finite2 entered2
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history3 finite3 entered3
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history4 finite4 entered4
  exact restores entered4

private lemma candidate_scopes_restore (width : Nat)
    (inner : Circuit model (Layout.context ctx width) (Layout.context ctx width))
    (Reference : Register)
    (restores : ∀ {History : Type} [Fintype History]
      (state : State (Layout.context ctx width) Reference (model.HiddenState × History)),
      inner.BorrowedRestored Reference state (inner.execute environment Reference state))
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (Layout.scopes ctx width inner).BorrowedRestored Reference state
      ((Layout.scopes ctx width inner).execute environment Reference state) := by
  unfold Layout.scopes
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history0 finite0 entered0
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history1 finite1 entered1
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history2 finite2 entered2
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history3 finite3 entered3
  exact restores entered3

private lemma selection_scopes_restore (width : Nat)
    (inner : Circuit model (SelectionLayout.context ctx width) (SelectionLayout.context ctx width))
    (Reference : Register)
    (restores : ∀ {History : Type} [Fintype History]
      (state : State (SelectionLayout.context ctx width) Reference (model.HiddenState × History)),
      inner.BorrowedRestored Reference state (inner.execute environment Reference state))
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (SelectionLayout.scopes ctx width inner).BorrowedRestored Reference state
      ((SelectionLayout.scopes ctx width inner).execute environment Reference state) := by
  unfold SelectionLayout.scopes
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history0 finite0 entered0
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history1 finite1 entered1
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history2 finite2 entered2
  apply Circuit.borrowedRestored_workspace (environment := environment)
  intro history3 finite3 entered3
  exact restores entered3

variable [BitWord.Selected model]

/-- Both complete checks, local selection and actual final conversion restore the borrowed state.
-/
lemma nativeQuadratic_checkedBody_borrowedRestored
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (LocalLayout.context ctx width) Reference (model.HiddenState × History)) :
    (checkedBody (model := model) modulus original).BorrowedRestored Reference state
      ((checkedBody (model := model) modulus original).execute environment Reference state) := by
  let pair := LocalLayout.pairRefs modulus
  exact Circuit.borrowedRestored_seq (environment := environment) (Pair.code (model := model) pair)
    (NarrowSelection.code (model := model) (FirstAccepted.cellRead pair.selection.accepted)
      (FirstAccepted.cellRead pair.selection.selected) (LocalLayout.persistentRefs original width))
    state (nativeQuadratic_pair_borrowedRestored pair Reference state)
    (NarrowSelection.nativeQuadratic_narrow_borrowedRestored
      (FirstAccepted.cellRead pair.selection.accepted)
      (FirstAccepted.cellRead pair.selection.selected) (LocalLayout.persistentRefs original width)
      Reference _)

/-- Actual candidate arithmetic and the five checker scopes preserve the complete borrowed state.
-/
lemma nativeQuadratic_candidateBody_borrowedRestored
    (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (LocalLayout.candidateContext ctx width) Reference
      (model.HiddenState × History)) :
    (candidateBody (model := model) input modulus original).BorrowedRestored Reference state
      ((candidateBody (model := model) input modulus original).execute environment
        Reference state) := by
  exact Circuit.borrowedRestored_seq (environment := environment)
    (Initialized.code (model := model) (LocalLayout.arithmeticRead input width)
      (LocalLayout.arithmeticRead modulus width) (LocalLayout.arithmeticRefs ctx width))
    (CheckLayout.scopes (LocalLayout.candidateContext ctx width) (RSA.quadraticWordWidth width)
      (checkedBody (model := model) modulus original)) state
    (nativeQuadratic_initialized_borrowedRestored (LocalLayout.arithmeticRead input width)
      (LocalLayout.arithmeticRead modulus width) (LocalLayout.arithmeticRefs ctx width)
      Reference state)
    (check_scopes_restore (RSA.quadraticWordWidth width)
      (checkedBody (model := model) modulus original) Reference
      (nativeQuadratic_checkedBody_borrowedRestored modulus original Reference) _)

/-- The complete actual quadratic program restores every arbitrary borrowed joint interface. -/
lemma nativeQuadratic_program_borrowedRestored (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (program (model := model) input modulus original).BorrowedRestored Reference state
      ((program (model := model) input modulus original).execute environment Reference state) := by
  apply selection_scopes_restore
  intro history historyFinite entered
  exact candidate_scopes_restore width
    (candidateBody (model := model) input modulus original) Reference
    (nativeQuadratic_candidateBody_borrowedRestored input modulus original Reference) entered

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
