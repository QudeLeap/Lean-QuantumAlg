/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition.Range
import all QuantumAlg.Core.Execution.Classical.Composition
import all QuantumAlg.Core.Execution.Reference.Observation
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Chronological composition of actual stored-reference kernels

Each component's native execution supplies its weighted-reference equation
and establishes the seed required by its successor. The finite composition
follows the actual increasing circuit indices and retains arbitrary caller
Store, hidden state, history and off-diagonal reference entries. Its hypotheses
are internal proved component laws, without an added public input condition.
-/

namespace QuantumAlg.Circuit

noncomputable section

open Execution

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
  {ctx : RuntimeCtx .quantum}

/-- Backward transport of one observation through the actual chronological component kernels. -/
def forRangeReferenceKernel : (count : Nat) →
    (Fin count → (Store ctx → ℂ) → Store ctx → ℂ) → (Store ctx → ℂ) → Store ctx → ℂ
  | 0, _kernels, weight => weight
  | count + 1, kernels, weight =>
      kernels 0 (forRangeReferenceKernel count (fun index => kernels index.succ) weight)

/-- Actual indexed execution composes its proved kernels on the internally established seed. -/
lemma forRange_referenceFiberSum (count : Nat)
    (body : Fin count → Circuit (.quantum gates oracles operations classicalOracles) ctx ctx)
    (environment : (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)
    (seed : ctx.register.Index)
    (kernels : Fin count → (Store ctx → ℂ) → Store ctx → ℂ)
    (seededAfter : ∀ index {Reference : Register} {History : Type} [Fintype History]
      (state : State ctx Reference (classicalOracles.HiddenState × History)),
      BasisSeeded.Holds seed ((body index).execute environment Reference state))
    (equations : ∀ index {Reference : Register} {History : Type} [Fintype History]
      (state : State ctx Reference (classicalOracles.HiddenState × History)),
      BasisSeeded.Holds seed state → ∀ (weight : Store ctx → ℂ) (left right : Reference.Index),
      ExecutionState.referenceFiberSum ((body index).execute environment Reference state)
          (fun entry _ => weight entry.1) left right =
        ExecutionState.referenceFiberSum state
          (fun entry _ => kernels index weight entry.1) left right)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (classicalOracles.HiddenState × History))
    (seeded : BasisSeeded.Holds seed state)
    (weight : Store ctx → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((forRange count body).execute environment Reference state)
        (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => forRangeReferenceKernel count kernels weight entry.1) left right := by
  induction count generalizing History with
  | zero =>
      rw [forRange, execute_id_mapClassical
        (model := .quantum gates oracles operations classicalOracles)]
      exact ExecutionState.referenceFiberSum_mapClassical state
        (fun entry => (entry.1, (entry.2.1, (entry.2.2, ()))))
        (fun entry _ => weight entry.1) left right
  | succ count ih =>
      rw [forRange, referenceFiberSum_execute_seq]
      rw [ih (fun index => body index.succ)
        (fun index => kernels index.succ) (fun index => seededAfter index.succ)
        (fun index => equations index.succ) ((body 0).execute environment Reference state)
        (seededAfter 0 state)]
      exact equations 0 state seeded
        (forRangeReferenceKernel count (fun index => kernels index.succ) weight) left right

end

end QuantumAlg.Circuit
