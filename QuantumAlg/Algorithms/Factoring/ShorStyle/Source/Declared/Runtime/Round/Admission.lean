/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Round.Protocol
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Entry
import all QuantumAlg.Core.Execution.Borrowed

/-!
# Actual complete predecessors establish independent next-round admission

The original initializer supplies zero support and latch absence. Every
complete recovery/feedback/reset predecessor supplies the next local zero
support and preserves latch soundness. These are genuine next inputs, with
the actual store and service state retained.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Round

open Execution

noncomputable section

/-- Real initialization admits the independent complete-round domain
without caller witnesses. -/
lemma initialized_admitted (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    {N : Nat} {environment : (executionModel N).Environment}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N) {Reference : Register}
    (original : OracleInput
      (executionModel N).classicalOracles base Reference) :
    inputDomain (Initialized.bank base noQuantum N) model (Initialized.cells base noQuantum N)
      (((Initialized.ready base noQuantum N).nextInput
        environment original).localState) := by
  constructor
  · exact Initialized.nextInput_local_support (environment := environment) base noQuantum N original
  · intro record positive
    exact Or.inr (Initialized.nextInput_latch_absent
        (environment := environment) base noQuantum N original record positive)

/-- The initializer's bank is owned while arbitrary borrowed classical/reference state survives. -/
lemma initialized_noBorrowedQuantum (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) :
    (Initialized.bank base noQuantum N).borrowedQuantumWires = [] := by
  have empty := base.borrowedQuantumWires_sublist
  rw [noQuantum] at empty
  exact (Initialized.ready base noQuantum N).borrowedQuantumWires_preserved.trans
    (List.sublist_nil.mp empty)

/-- Actual complete feedback supplies both local obligations for its genuine successor. -/
lemma nextInput_admitted (ctx : RuntimeCtx .quantum) {N : Nat}
    (model : NumberTheory.Factoring.SemiprimeFactorModel N)
    (sameWires : ctx.quantumWires = (layout N).wires) (cells : NativeFactorScan.Cells ctx N)
    (result : CWriteRef ctx (.option (.unsignedWord (modulusBits N))))
    (separated : NativeFactorScan.Separated cells result) {Reference : Register}
    (original : OracleInput
      (executionModel N).classicalOracles ctx Reference)
    (admitted : inputDomain ctx model cells original.localState) :
    inputDomain (Iteration.context ctx N) model (Completion.cells ctx N cells)
      (((Completion.code ctx N (Probability.Input.ofSemiprimeModel model)
        sameWires cells result).nextInput
          (environment (Probability.Input.ofSemiprimeModel model)) original).localState) :=
  ⟨Completion.nextInput_local_support
      (environment := environment (Probability.Input.ofSemiprimeModel model))
      ctx N (Probability.Input.ofSemiprimeModel model) sameWires cells result original,
    Completion.nextInput_latch_sound ctx model sameWires cells result separated original
      admitted.1 admitted.2⟩

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Round
