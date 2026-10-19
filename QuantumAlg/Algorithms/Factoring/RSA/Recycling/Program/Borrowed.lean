/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.RSA.Recycling.Program
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Core.Execution.Borrowed
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Algorithm.Borrowed

/-!
# Complete borrowed restoration for the actual recycled RSA parent

The incoming context may contain arbitrary borrowed classical values jointly
correlated with an external reference. The existing no-quantum input condition
excludes borrowed quantum wires, not classical values or reference systems.
The structural restoration law applies directly to the new parent's actual
code, including its zero-count branch, allocation, stored dispatch, measurements,
classical recovery and selection. Recording the original input as run history
preserves this same joint borrowed observation.
-/

namespace QuantumAlg.Factoring.RSA.Recycling.Program

noncomputable section

variable {environment : ShortDLP.CompiledMAU.Recycling.model.Environment}

open Execution
open EkeraHastadStyle.Canonical

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N : Nat)

include noQuantum in
private lemma incoming_noBorrowedQuantum : base.borrowedQuantumWires = [] := by
  have subset := base.borrowedQuantumWires_sublist
  rw [noQuantum] at subset
  exact List.sublist_nil.mp subset

/-- The actual parent code restores the complete borrowed classical-reference state. -/
lemma rsaRecyclingParent_code_borrowedRestored (input : Input N) (count : Nat)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State base Reference (ShortDLP.CompiledMAU.Recycling.model.HiddenState × History)) :
    (run base noQuantum N input count).code.BorrowedRestored Reference state
      ((run base noQuantum N input count).code.execute environment Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (environment := environment)
    (run base noQuantum N input count).code
    (incoming_noBorrowedQuantum base noQuantum) Reference state

/-- The complete run restores every borrowed correlation for every natural batch count. -/
lemma rsaRecyclingParent_restoresBorrowed (input : Input N) (count : Nat)
    {Reference : Register}
    (original : OracleInput ShortDLP.CompiledMAU.Recycling.model.classicalOracles base Reference) :
    (run base noQuantum N input count).RestoresBorrowed environment original := by
  apply AlgorithmRun.restoresBorrowed_of_circuit (environment := environment)
  intro reference history _ state
  exact rsaRecyclingParent_code_borrowedRestored base noQuantum N input count reference state

end

end QuantumAlg.Factoring.RSA.Recycling.Program
