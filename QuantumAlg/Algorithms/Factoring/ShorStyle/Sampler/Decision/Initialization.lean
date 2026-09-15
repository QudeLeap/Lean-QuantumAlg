/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Store.Read

/-!
# Actual initialization of the residue decision fields

The four real instructions preserve the selected candidate before loading
the default one word and clearing the factor flag. These values are proved
from the actual writes, independently of every incoming scratch value. At
width zero the stored one has the same intrinsic wrapping interpretation as
the native increment; the public nontrivial modulus supplies positive width.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- A real self-XOR writes the complete zero word, whatever the initial target was. -/
theorem decision_clearWord_read (output : CWriteRef ctx (.unsignedWord width))
    (store : Store ctx) :
    (store.applyOp (clearWordOp output)).read (FirstAccepted.cellRead output) =
      CShape.wordOfNat width 0 := by
  have actual := Store.read_applyOp_output store (clearWordOp output)
  change (store.applyOp (clearWordOp output)).read (FirstAccepted.cellRead output) =
    CShape.wordOfNat width ((store.read (FirstAccepted.cellRead output)).toNat ^^^
      (store.read (FirstAccepted.cellRead output)).toNat) at actual
  simpa only [Nat.xor_self] using actual

/-- A real Boolean self-XOR overwrites its target with false. -/
theorem decision_clearBit_read (output : CWriteRef ctx .bit) (store : Store ctx) :
    (store.applyOp (clearBitOp output)).read (FirstAccepted.cellRead output) = .bit false := by
  have actual := Store.read_applyOp_output store (clearBitOp output)
  change (store.applyOp (clearBitOp output)).read (FirstAccepted.cellRead output) =
    Resource.BitOpcode.eval .xor (.product (store.read (FirstAccepted.cellRead output))
      (store.read (FirstAccepted.cellRead output))) at actual
  cases value : store.read (FirstAccepted.cellRead output) with
  | bit bit =>
      rw [value] at actual
      cases bit <;> exact actual

/-- Exact store after preserving the candidate, loading one, and clearing the tag. -/
def initializationStore (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width) (store : Store ctx) : Store ctx :=
  (((store.applyOp (.wordUnary .copy width ctx
    (FirstAccepted.cellRead shared.selector.selected) scratch.candidate)).applyOp
      (clearWordOp shared.selector.selected)).applyOp (.wordUnary .increment width ctx
        (FirstAccepted.cellRead shared.selector.selected) shared.selector.selected)).applyOp
          (clearBitOp scratch.eligible)

/-- Actual initialization preserves every complete quantum-reference block with its real path. -/
theorem decisionInitialization_execute (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (initializeBody shared scratch).execute Reference state =
      state.mapClassical (fun entry =>
        (initializationStore shared scratch entry.1, (entry.2, ((), ((), ((), ())))))) := by
  simp only [initializeBody, Circuit.execute_seq, Circuit.execute_classical_mapClassical,
    State.mapHistory, ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  congr 1
  exact Subsingleton.elim _ _

private theorem preserves_cell {input output observed : CShape}
    (op : ClassicalOp input output ctx ctx) (other : CWriteRef ctx observed)
    (different : op.outputRef.key ≠ other.key) (store : Store ctx) :
    (store.applyOp op).read (FirstAccepted.cellRead other) =
      store.read (FirstAccepted.cellRead other) :=
  Store.read_write_other store op.outputRef other.toCStorageRef _ different

/-- The actual three output cells contain the preserved candidate, wrapping one, and false tag. -/
theorem decisionInitialization_values (shared : Proposal.SharedRefs ctx width)
    (scratch : Proposal.ScratchRefs ctx width)
    (candidateUnit : scratch.candidate.key ≠ shared.selector.selected.key)
    (flagUnit : scratch.eligible.key ≠ shared.selector.selected.key)
    (flagCandidate : scratch.eligible.key ≠ scratch.candidate.key) (store : Store ctx) :
    let final := initializationStore shared scratch store
    final.read (FirstAccepted.cellRead scratch.candidate) =
        store.read (FirstAccepted.cellRead shared.selector.selected) ∧
      final.read (FirstAccepted.cellRead shared.selector.selected) = CShape.wordOfNat width 1 ∧
        final.read (FirstAccepted.cellRead scratch.eligible) = .bit false := by
  let copied := store.applyOp (.wordUnary .copy width ctx
    (FirstAccepted.cellRead shared.selector.selected) scratch.candidate)
  let cleared := copied.applyOp (clearWordOp shared.selector.selected)
  let increment : ClassicalOp (.unsignedWord width) (.unsignedWord width) ctx ctx :=
    .wordUnary .increment width ctx
      (FirstAccepted.cellRead shared.selector.selected) shared.selector.selected
  have copiedRead : copied.read (FirstAccepted.cellRead scratch.candidate) =
      store.read (FirstAccepted.cellRead shared.selector.selected) :=
    Store.read_applyOp_output store (.wordUnary .copy width ctx
      (FirstAccepted.cellRead shared.selector.selected) scratch.candidate)
  have loaded : (cleared.applyOp increment).read
      (FirstAccepted.cellRead shared.selector.selected) = CShape.wordOfNat width 1 := by
    have actual := Store.read_applyOp_output cleared increment
    change (cleared.applyOp increment).read (FirstAccepted.cellRead shared.selector.selected) =
      CShape.wordOfNat width
        ((cleared.read (FirstAccepted.cellRead shared.selector.selected)).toNat + 1)
        at actual
    rw [decision_clearWord_read] at actual
    simpa only [CShape.wordOfNat_val, Nat.zero_mod, Nat.zero_add] using actual
  refine ⟨?_, ?_, ?_⟩
  · exact (preserves_cell (clearBitOp scratch.eligible) scratch.candidate flagCandidate _).trans
      ((preserves_cell increment scratch.candidate candidateUnit.symm _).trans
        ((preserves_cell (clearWordOp shared.selector.selected) scratch.candidate
          candidateUnit.symm copied).trans copiedRead))
  · exact (preserves_cell (clearBitOp scratch.eligible)
      shared.selector.selected flagUnit _).trans loaded
  · exact decision_clearBit_read scratch.eligible _

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Decision
