/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Uniform.Step

/-!
# Uniform replacement on the same arbitrary mathematical source carrier

The factorization premise concerns only preparation on the mathematical
source. Both surrounding programs remain their literal actual executions.
Their complete Store, service state, measured Paths and external Reference
are retained. A concrete consumer must establish the factorization and zero
support internally; these are not new assumptions of a sampling endpoint.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {S Rest : Register} {totalBits active : Nat}

private lemma commute_state {Record : Type} [Fintype Record] {R : Register}
    (state : ExecutionState Record R) (first second : UnitaryOperator R)
    (commute : first * second = second * first) :
    (state.applyUnitary (fun _ => first)).applyUnitary (fun _ => second) =
      (state.applyUnitary (fun _ => second)).applyUnitary (fun _ => first) := by
  apply ExecutionState.ext
  intro record
  change DensityOperator.applyUnitary second
      (DensityOperator.applyUnitary first (state.block record)) =
    DensityOperator.applyUnitary first
      (DensityOperator.applyUnitary second (state.block record))
  exact (DensityOperator.applyUnitary_mul second first (state.block record)).symm.trans
    ((congrArg (fun operator : UnitaryOperator R =>
      DensityOperator.applyUnitary operator (state.block record)) commute.symm).trans
        (DensityOperator.applyUnitary_mul first second (state.block record)))

/-- A proved source factorization gives one exact actual-interpreter replacement on any carrier. -/
lemma window_source_uniform_factor_step (ports : Ports ctx totalBits active)
    (partition : S.Index ≃ (Qubits active).Index × Rest.Index) (Reference : Register)
    (future : UnitaryOperator S) (tail : UnitaryOperator (Rest.prod Reference))
    (first last : Circuit (.quantum AlgorithmGate.model .empty operations services) ctx ctx true)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment)
    {History : Type} [Fintype History]
    (state : State ctx (S.prod Reference) (services.HiddenState × History))
    (firstNatural : first.execute environment _
        (state.applyUnitary (fun _ => sourcePreparationAction Reference future)) =
      (first.execute environment _ state).applyUnitary
        (fun _ => sourcePreparationAction Reference future))
    (factor : (first.execute environment _ state).applyUnitary
        (fun _ => sourcePreparationAction Reference future) =
      ((first.execute environment _ state).applyUnitary
        (fun _ => referencePreparation partition Reference)).applyUnitary
          (fun _ => savedPreparation partition Reference tail))
    (supported : ∀ record label, ¬doubleZero ports partition Reference label →
      ((first.execute environment _ state).block record).matrix label label = 0)
    (lastNatural : ∀ current : State ctx (S.prod Reference)
        (services.HiddenState × (History × first.Path)),
      last.execute environment _ (current.applyUnitary
          (fun _ => savedPreparation partition Reference tail)) =
        (last.execute environment _ current).applyUnitary
          (fun _ => savedPreparation partition Reference tail)) :
    last.execute environment _
        ((first.execute environment _
          (state.applyUnitary (fun _ => sourcePreparationAction Reference future))).applyUnitary
            (fun _ => selectedFeedOperator ports partition Reference)) =
      (last.execute environment _
        ((first.execute environment _ state).applyUnitary (fun _ =>
          UnitaryOperator.prodTensor ((preparation active ports).matrix environment.quantum)
            (1 : UnitaryOperator (S.prod Reference))))).applyUnitary
              (fun _ => savedPreparation partition Reference tail) := by
  rw [firstNatural, factor]
  rw [commute_state _ (savedPreparation partition Reference tail)
    (selectedFeedOperator ports partition Reference)
    (window_source_feed_saved_commute ports partition Reference tail).symm]
  rw [window_source_prepared_feed_state ports partition environment.quantum Reference
    (first.execute environment _ state) supported]
  exact lastNatural _

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
