/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Execution
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Complete borrowed restoration of the actual native Shor run

The input has no supplied quantum systems. The complete real preparation,
sampling, measurement, reset and classical recovery circuit therefore acts
on owned quantum systems throughout. Its actual interpretation restores the
entire borrowed classical-reference observation, including all correlations;
the full result and every retained sample remain in its complete output.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The sole complete circuit preserves the entire borrowed classical-reference interface. -/
theorem code_borrowedRestored {N : Nat} (source : Input N) (count : Nat) (Reference : Register)
    {History : Type} [Fintype History] (state : State pre Reference History) :
    (code source count).BorrowedRestored Reference state
      ((code source count).execute Reference state) := by
  have noBorrowed : pre.borrowedQuantumWires = [] := by
    have subset := pre.borrowedQuantumWires_sublist
    rw [pre_quantumWires] at subset
    exact List.sublist_nil.mp subset
  exact Circuit.borrowedRestored_of_noBorrowedQuantum
    (code source count) noBorrowed Reference state

/-- Mandatory restoration is proved for the same actual run and arbitrary external reference. -/
theorem run_restoresBorrowed {N : Nat} (source : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input pre Reference) :
    (run source count).RestoresBorrowed input :=
  code_borrowedRestored source count Reference
    (input.state.mapClassical (fun store => (store, store)))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint
