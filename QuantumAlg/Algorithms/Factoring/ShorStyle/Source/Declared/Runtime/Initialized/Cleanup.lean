/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Solves
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Cleanup
import all QuantumAlg.Core.Execution.Restart.Sequence
import all QuantumAlg.Core.Execution.Input.Successor.Sequence

/-!
# Complete first-cycle restart and genuine successor admission

The full initial computation includes preparation and the complete first
attempt. Its actual terminal physical reset supplies every owned record's
fixed seed. The next complete round consumes its actual full output, retaining
the store, service and external reference instead of requesting a fresh input.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized

open Execution

noncomputable section

/-- The actual first-round output admits the next complete round without a new seed witness. -/
lemma nextInput_admitted (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N) {Reference : Register}
    (original : OracleInput
      (executionModel N).classicalOracles base Reference) :
    Round.inputDomain (Iteration.context (bank base noQuantum N) N) model
      (Completion.cells (bank base noQuantum N) N (cells base noQuantum N))
      ((code base noQuantum N (Probability.Input.ofSemiprimeModel model)).nextInput
        (environment (Probability.Input.ofSemiprimeModel model)) original).localState := by
  let input := Probability.Input.ofSemiprimeModel model
  have actual := Round.nextInput_admitted (bank base noQuantum N) model
    (bank_wires base noQuantum N) (cells base noQuantum N) (result base noQuantum N)
    (Initialized.separated base noQuantum N) ((ready base noQuantum N).nextInput (environment
      input) original)
    (Round.initialized_admitted (environment := environment input) base noQuantum model original)
  simpa only [code, Circuit.nextInput_seq] using actual

/-- The first cycle's genuine reset supplies full restoration and fixed-record restart. -/
lemma restartCleanup (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (N : Nat) (input : Input N) {environment : (executionModel N).Environment} :
    Circuit.RestartCleanup (code base noQuantum N input) environment :=
  Circuit.RestartCleanup.after (environment := environment) (ready base noQuantum N)
    (Completion.code (bank base noQuantum N) N input (bank_wires base noQuantum N)
      (cells base noQuantum N) (result base noQuantum N))
    (fun Reference {_} _ state => Circuit.borrowedRestored_of_noBorrowedQuantum
      (ready base noQuantum N) environment (base_noBorrowedQuantum base noQuantum) Reference state)
    (Round.restartCleanup (environment := environment) (bank base noQuantum N) N input
      (bank_wires base noQuantum N)
      (cells base noQuantum N) (result base noQuantum N)
      (Round.initialized_noBorrowedQuantum base noQuantum N))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized
