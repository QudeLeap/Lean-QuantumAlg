/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Random.Discard
import all QuantumAlg.Core.Execution.Borrowed.Preservation

/-!
# Borrowed restoration by actual random-bit instructions

The instruction writes its sample only to the supplied writable cell.
Borrowed classical values are therefore unchanged. Summing the independent
sample restores their full prior joint quantum-reference observation, with
no initialization premise on the written cell or any other system.
-/

namespace QuantumAlg.Circuit

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Real random-bit generation restores all borrowed classical-quantum-reference correlations. -/
theorem borrowedRestored_randomBits {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (width : Nat) (output : CWriteRef ctx (.bits width)) {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (Circuit.randomBits width output).BorrowedRestored Reference state
      ((Circuit.randomBits width output).execute Reference state) := by
  rw [BorrowedRestored, observeBorrowedAfter_sameContext]
  change observeBorrowed Reference (State.randomBits state width output) =
    observeBorrowed Reference state
  apply ExecutionState.ext
  intro value
  rw [observeBorrowed_block, observeBorrowed_block]
  have observed :
      (State.randomBits state width output).mapClassical
          (fun entry => entry.1.readBorrowedClassical) =
        state.mapClassical (fun entry => entry.1.readBorrowedClassical) := by
    refine Eq.trans ?_ (uniformChoice_map_ignore state
      ⟨2 ^ width, Nat.two_pow_pos width⟩ (fun entry => entry.1.readBorrowedClassical))
    simp only [State.randomBits, ExecutionState.executionState_mapClassical_comp,
      Function.comp_def, Store.readBorrowedClassical_write]
  exact congrArg (fun classical : ExecutionState ctx.borrowedClassicalShape.Value
    (Register.prod ctx.register Reference) =>
      ctx.observeBorrowedWithReference Reference (classical.block value)) observed

end

end QuantumAlg.Circuit
