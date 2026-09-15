/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Empty
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Correctness

/-!
# Actual finite retry for every natural total batch count

Zero batches retain the actual empty optional result. A positive count runs
the existing first batch, same-bank continuation and chronological selection.
Both branches retain the original scientific input domain and complete output
manifest. The natural count chooses between the existing actual circuits.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

/-- The actual final live context is selected structurally by the total batch count. -/
public def context (N : Nat) : Nat → RuntimeCtx .quantum
  | 0 => NativeRetryEmpty.context base N
  | count + 1 =>
      NativeRetrySelection.context (NativeRetryChain.context base noQuantum N count) N

/-- Zero batches retain only the existing actual empty-result allocation. -/
theorem context_zero (N : Nat) :
    context base noQuantum N 0 = NativeRetryEmpty.context base N := rfl

/-- A positive total retains the exact first-batch, continuation and selection context. -/
theorem context_succ (N count : Nat) :
    context base noQuantum N (count + 1) =
      NativeRetrySelection.context (NativeRetryChain.context base noQuantum N count) N := rfl

variable {N : Nat}

/-- The finite entry executes exactly the existing actual circuit for its total batch count. -/
def code (input : Input N) : (totalRounds : Nat) →
    Circuit base (context base noQuantum N totalRounds)
  | 0 => NativeRetryEmpty.code base N
  | count + 1 => NativeRetrySelection.code base noQuantum input count

/-- The zero-count code is definitionally the actual empty-result allocation. -/
theorem code_zero (input : Input N) :
    code base noQuantum input 0 = NativeRetryEmpty.code base N := rfl

/-- The positive-count code is definitionally the existing selected batch-chain execution. -/
theorem code_succ (input : Input N) (count : Nat) :
    code base noQuantum input (count + 1) =
      NativeRetrySelection.code base noQuantum input count := rfl

/-- The complete finite run preserves the original optional-factor result shape. -/
def run (input : Input N) : (totalRounds : Nat) →
    AlgorithmRun base (context base noQuantum N totalRounds)
      (LatticeBatchRecoveryOutput.OutputShape N)
  | 0 => NativeRetryEmpty.run base N
  | count + 1 => NativeRetrySelection.run base noQuantum input count

/-- The zero-count run is definitionally the complete actual empty-result run. -/
theorem run_zero (input : Input N) :
    run base noQuantum input 0 = NativeRetryEmpty.run base N := rfl

/-- The positive-count run is definitionally the original chronological selection run. -/
theorem run_succ (input : Input N) (count : Nat) :
    run base noQuantum input (count + 1) =
      NativeRetrySelection.run base noQuantum input count := rfl

/-- The complete run executes exactly the same structurally selected actual code. -/
theorem run_code (input : Input N) (totalRounds : Nat) :
    (run base noQuantum input totalRounds).code = code base noQuantum input totalRounds := by
  cases totalRounds <;> rfl

/-- Every branch lists all original and actually retained live entries. -/
theorem output_listing (input : Input N) (totalRounds : Nat) :
    (run base noQuantum input totalRounds).output.listing =
      (context base noQuantum N totalRounds).keys := by
  cases totalRounds with
  | zero => exact NativeRetryEmpty.output_listing base N
  | succ count => exact NativeRetrySelection.output_listing base noQuantum input count

/-- Every finite actual execution jointly restores arbitrary borrowed resources and references. -/
theorem code_borrowedRestored (input : Input N) (totalRounds : Nat) (Reference : Register)
    {History : Type} [Fintype History] (state : State base Reference History) :
    (code base noQuantum input totalRounds).BorrowedRestored Reference state
      ((code base noQuantum input totalRounds).execute Reference state) := by
  cases totalRounds with
  | zero =>
      exact Circuit.borrowedRestored_retain base.canonicalFreshKey
        (LatticeBatchRecoveryOutput.OutputShape N) base.canonicalFreshKey_fresh state
  | succ count =>
      exact NativeRetrySelection.code_borrowedRestored base noQuantum input count Reference state

/-- The actual complete finite run preserves the same borrowed interface for every input state. -/
theorem run_restoresBorrowed (specification : Input N) (totalRounds : Nat)
    {Reference : Register} (input : Execution.Input base Reference) :
    (run base noQuantum specification totalRounds).RestoresBorrowed input := by
  cases totalRounds with
  | zero => exact NativeRetryEmpty.run_restoresBorrowed base N input
  | succ count =>
      exact NativeRetrySelection.code_borrowedRestored base noQuantum specification count Reference
        (input.state.mapClassical (fun store => (store, store)))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
