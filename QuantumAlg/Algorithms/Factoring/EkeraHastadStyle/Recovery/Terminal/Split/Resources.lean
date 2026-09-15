/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Terminal.Split
import all QuantumAlg.Components.Classical.TerminalDecode.Retained.Semantics
import Mathlib.Data.Fintype.Prod

/-!
# Literal native costs and borrowed restoration of terminal splitting

The independent allowance charges the original terminal decoder, both real
resizes, and every actual right shift. The workspace itself contributes no
instruction. Restoration follows the same decoder and native instructions
on the complete borrowed classical-quantum-reference interface.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit

open Execution
open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell : Nat}

/-- Independent native coordinates for the decoder and the original extraction sequence. -/
def nativeEnvelope (kind : ProblemKind) (m ell : Nat) : ResourcePool kind :=
  TerminalDecode.envelope ((ell + m) + ell) +
    (ResourcePool.singleton (.classicalOperation (.wordResize ((ell + m) + ell) ell)) +
      (TerminalShift.nativeEnvelope kind ((ell + m) + ell) ell +
        ResourcePool.singleton (.classicalOperation (.wordResize ((ell + m) + ell) (ell + m)))))

/-- The real trace retains the decoder path, low resize, all shifts and high resize in order. -/
theorem nativeRecovery_terminal_split_eventTrace
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (path : (code input refs).Path) :
    (code input refs).eventTrace path =
      (terminalCircuit (underRead input m ell) (full ctx m ell)).eventTrace path.1 ++
        ([.classicalOperation (.wordResize ((ell + m) + ell) ell)] ++
          (List.replicate ell (.classicalOperation (.wordUnary .shiftRight ((ell + m) + ell))) ++
            [.classicalOperation (.wordResize ((ell + m) + ell) (ell + m))])) :=
  congrArg (fun events : List (Resource.Event kind) =>
    (terminalCircuit (underRead input m ell) (full ctx m ell)).eventTrace path.1 ++
      ([.classicalOperation (.wordResize ((ell + m) + ell) ell)] ++
        (events ++ [.classicalOperation (.wordResize ((ell + m) + ell) (ell + m))])))
    (TerminalShift.nativeRecovery_terminal_shifts_trace ell (full ctx m ell) path.2.2.1)

/-- Every actual path fits the independent budget at every native event coordinate. -/
theorem nativeRecovery_terminal_split_pool_le
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (path : (code input refs).Path) :
    (code input refs).resourcePool path ≤ nativeEnvelope kind m ell := by
  rw [Circuit.resourcePool, nativeRecovery_terminal_split_eventTrace,
    ResourcePool.ofList_append, ResourcePool.ofList_append, ResourcePool.ofList_append]
  exact add_le_add
    (nativeRecovery_terminal_pool_le (underRead input m ell) (full ctx m ell) path.1)
    (add_le_add le_rfl (add_le_add le_rfl le_rfl))

/-- The independent allowance has one entry per possible decoder instruction and real extraction.
-/
theorem nativeRecovery_terminal_split_envelope_card (kind : ProblemKind) (m ell : Nat) :
    (nativeEnvelope kind m ell).card = 2 * ((ell + m) + ell) + ell + 2 := by
  simp only [nativeEnvelope, TerminalDecode.envelope, TerminalDecode.bitEnvelope,
    TerminalShift.nativeEnvelope, ResourcePool.scale, ResourcePool.singleton, ResourcePool.ofList,
    Multiset.card_add, Multiset.card_nsmul, Multiset.card_replicate, Multiset.coe_card,
    List.length_replicate]
  omega

/-- The actual serial dependency charges both conversions and every real decoder and shift step.
-/
theorem nativeRecovery_terminal_split_depth_le
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (path : (code input refs).Path) :
    (code input refs).depth (fun _ => 1) path ≤ 2 * ((ell + m) + ell) + ell + 2 := by
  have decoder := nativeRecovery_terminal_depth_le
    (underRead input m ell) (full ctx m ell) path.1
  have shifts := TerminalShift.nativeRecovery_terminal_shifts_depth ell
    (full ctx m ell) (fun _ => 1) path.2.2.1
  change (terminalCircuit (underRead input m ell) (full ctx m ell)).depth (fun _ => 1) path.1 +
    (1 + ((TerminalShift.code ell (full ctx m ell)).depth (fun _ => 1) path.2.2.1 + 1)) ≤ _
  omega

private theorem body_borrowedRestored
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (context ctx m ell) Reference History) :
    (body input refs).BorrowedRestored Reference state
      ((body input refs).execute Reference state) := by
  -- Keep every sequence index at the named body context before instantiating
  -- the surrounding workspace's definitionally equal allocation context.
  unfold body
  apply Circuit.borrowedRestored_seq (ctx := context ctx m ell)
    (middle := context ctx m ell) (post := context ctx m ell)
  · exact TerminalDecode.fold_borrowedRestored (full ctx m ell)
      (List.ofFn (fun index => CInputRef.bitsGet (underRead input m ell) index)) Reference state
  · apply Circuit.borrowedRestored_seq
    · exact Circuit.borrowedRestored_classical (lowOp refs) _
    · apply Circuit.borrowedRestored_seq
      · exact TerminalShift.nativeRecovery_terminal_shifts_borrowedRestored
          ell (full ctx m ell) Reference _
      · exact Circuit.borrowedRestored_classical (highOp refs) _

/-- The actual scoped extraction restores the complete borrowed interface on every reference. -/
theorem nativeRecovery_terminal_split_borrowedRestored
    (input : CInputRef ctx (.bits ((ell + m) + ell))) (refs : Refs ctx m ell)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    (code input refs).BorrowedRestored Reference state
      ((code input refs).execute Reference state) := by
  exact Circuit.borrowedRestored_workspace ctx.canonicalFreshKey
    (.unsignedWord ((ell + m) + ell)) ctx.canonicalFreshKey_fresh (body input refs) Reference
    (fun current => body_borrowedRestored input refs Reference current) state

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.TerminalSplit
