/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Step

/-!
# Structural source observations for a list of actual measured windows

Every stage retains both actual circuit Paths, the entire original Store,
service state and history. The only non-Circuit operation is the mathematical
source feed. Pulling an observable through the list gives an intrinsically
positive contraction on all source labels. This construction makes no
arithmetic correctness or uniform physical-preparation assertion.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel} {Reference : Register}

/-- One real reset, one mathematical source feed, and the real measured window middle. -/
structure Stage (ctx : RuntimeCtx .quantum) (operations : ClassicalOpModel)
    (services : ClassicalOracleModel) (Reference : Register) where
  first : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx true
  feed : UnitaryOperator (ctx.register.prod Reference)
  last : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx true

namespace Stage

/-- Every original history and both real chronological paths survive each stage. -/
def Records : List (Stage ctx operations services Reference) → Type → Type
  | [], History => History
  | stage :: rest, History => Records rest ((History × stage.first.Path) × stage.last.Path)

instance recordsFintype (stages : List (Stage ctx operations services Reference))
    (History : Type) [Fintype History] : Fintype (Records stages History) := by
  induction stages generalizing History with
  | nil => exact inferInstanceAs (Fintype History)
  | cons stage rest ih =>
      exact ih ((History × stage.first.Path) × stage.last.Path)

/-- The same actual interpreters, with a mathematical source feed between them at each node. -/
def run (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
    services).Environment) :
    (stages : List (Stage ctx operations services Reference)) →
      {History : Type} → [Fintype History] →
      State ctx Reference (services.HiddenState × History) →
        State ctx Reference (services.HiddenState × Records stages History)
  | [], _, _, state => state
  | stage :: rest, _, _, state => run environment rest
      (stage.last.execute environment Reference
        ((stage.first.execute environment Reference state).applyUnitary (fun _ => stage.feed)))

/-- Backward structural composition of the actual source observations on complete records. -/
def observation (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
    services).Environment) :
    (stages : List (Stage ctx operations services Reference)) →
      {History : Type} →
      Circuit.EffectFamily ctx Reference (services.HiddenState × Records stages History) →
        Circuit.EffectFamily ctx Reference (services.HiddenState × History)
  | [], _, effects => effects
  | stage :: rest, _, effects =>
      stepObservable Reference stage.feed stage.first stage.last environment
        (observation environment rest effects)

/-- Exact mixed-state event weight, proved by list induction without unfolding any circuit body. -/
lemma window_sourceSequence_weight
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (stages : List (Stage ctx operations services Reference))
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (effects : Circuit.EffectFamily ctx Reference
      (services.HiddenState × Records stages History)) :
    (run environment stages state).effectWeight effects =
      state.effectWeight (observation environment stages effects) := by
  induction stages generalizing History with
  | nil => rfl
  | cons stage rest ih =>
      exact (ih
        (stage.last.execute environment Reference
          ((stage.first.execute environment Reference state).applyUnitary
            (fun _ => stage.feed))) effects).trans
        (window_sourceStep_state_weight Reference stage.feed stage.first stage.last
          environment (observation environment rest effects) state)

end Stage

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
