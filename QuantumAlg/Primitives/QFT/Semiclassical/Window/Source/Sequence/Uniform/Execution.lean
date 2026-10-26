/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Prepared.Execution

/-!
# Structural composition of exact uniform-source replacements

This induction combines an exact head identity and an invariant of the
original prepared execution. Both are explicit proof premises to discharge
from the concrete source coordinates and the actual circuit laws. The source
run and prepared run retain their same real first/last Paths and complete
records. No arbitrary action is substituted for an actual interpreter, and
no source register is physically allocated by this mathematical identity.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {Reference : Register}

/-- Exact head replacement composes on the original list without unfolding any circuit body. -/
lemma window_source_uniform_sequence
    {Index : Type} (stage : Index → PreparedStage ctx operations services Reference)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment)
    (preparation : List Index → UnitaryOperator (ctx.register.prod Reference))
    (empty : preparation [] = 1)
    (admissible : List Index → Prop)
    (remaining : ∀ head rest, admissible (head :: rest) → admissible rest)
    (condition : {History : Type} → [Fintype History] →
      State ctx Reference (services.HiddenState × History) → Prop)
    (headIdentity : ∀ (head : Index) (rest : List Index),
      admissible (head :: rest) →
      ∀ {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)), condition state →
      (stage head).stage.last.execute environment Reference
          (((stage head).stage.first.execute environment Reference
            (state.applyUnitary (fun _ => preparation (head :: rest)))).applyUnitary
              (fun _ => (stage head).stage.feed)) =
        ((stage head).runHead environment state).applyUnitary (fun _ => preparation rest))
    (preserved : ∀ (head : Index) (rest : List Index),
      admissible (head :: rest) →
      ∀ {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
      condition state → condition ((stage head).runHead environment state))
    (indices : List Index)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (supported : condition state)
    (valid : admissible indices) :
    Stage.run environment ((indices.map stage).map PreparedStage.stage)
        (state.applyUnitary (fun _ => preparation indices)) =
      PreparedStage.run environment (indices.map stage) state := by
  revert valid
  induction indices generalizing History with
  | nil =>
      intro _
      change state.applyUnitary (fun _ => preparation []) = state
      rw [empty]
      apply ExecutionState.ext
      intro record
      exact DensityOperator.applyUnitary_one (state.block record)
  | cons head rest ih =>
      intro valid
      change Stage.run environment ((rest.map stage).map PreparedStage.stage)
        ((stage head).stage.last.execute environment Reference
          (((stage head).stage.first.execute environment Reference
            (state.applyUnitary (fun _ => preparation (head :: rest)))).applyUnitary
              (fun _ => (stage head).stage.feed))) = _
      rw [headIdentity head rest valid state supported]
      exact ih ((stage head).runHead environment state) (preserved head rest valid state supported)
        (remaining head rest valid)

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
