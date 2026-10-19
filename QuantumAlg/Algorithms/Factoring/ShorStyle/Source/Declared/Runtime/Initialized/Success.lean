/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Solves
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Admission
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Geometry
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Prefix

/-!
# Original success of the genuinely initialized complete first round

The actual prefix allocates and clears the latch and prepares its own bank.
Its real joint output supplies the complete round's local domain. The prefix
transport retains arbitrary incoming stores, services and external references;
no independent or replaced input is used to prove the original factor floor.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized

open Execution

noncomputable section

/-- The true first complete execution reaches the original unknown-prime factor threshold. -/
lemma relational_success (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    {N : Nat} (model : NumberTheory.Factoring.SemiprimeFactorModel N) {Reference : Register}
    (original : OracleInput
      (executionModel N).classicalOracles base Reference) :
    Probability.honestAttemptSuccessFloor N ≤
      ((run base noQuantum N (Probability.Input.ofSemiprimeModel model)).relationalDistribution
        (environment (Probability.Input.ofSemiprimeModel model)) original).toOuterMeasure
          {pair | Round.accepts model pair.2} := by
  let input := Probability.Input.ofSemiprimeModel model
  exact AlgorithmRun.relationalSuccess_after_prefix (ready base noQuantum N)
    (Round.algorithm (bank base noQuantum N) N input (bank_wires base noQuantum N)
      (cells base noQuantum N) (result base noQuantum N)).run (environment input) original
    {pair | Round.accepts model pair.2} {value | Round.accepts model value}
    (Probability.honestAttemptSuccessFloor N)
    (Round.relational_success (bank base noQuantum N) model (bank_wires base noQuantum N)
      (cells base noQuantum N) (result base noQuantum N) (Initialized.separated base noQuantum N)
      ((ready base noQuantum N).nextInput (environment input) original)
      (Round.initialized_admitted (environment := environment input) base noQuantum model original))
    (fun _ accepted => accepted)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Initialized
