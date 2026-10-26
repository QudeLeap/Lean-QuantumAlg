/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Base.Tensor.Reference

/-!
# Composing actual stored-value unitaries and exact chronological records

Each component equation concerns the same existing circuit and retains its
complete native path and actual next Store. The second unitary is evaluated
on that real next Store. The resulting equation keeps every original joint
block and arbitrary external reference, including classical overwrite fibers.
-/

namespace QuantumAlg

noncomputable section

local instance {A : Type} : DecidableEq A := Classical.decEq A

namespace ExecutionState

/-- Store-dependent unitary actions compose on each unchanged original classical block. -/
lemma executionState_applyUnitary_comp {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (first second : C → UnitaryOperator R) :
    (state.applyUnitary first).applyUnitary second =
      state.applyUnitary (fun entry => second entry * first entry) := by
  apply ExecutionState.ext
  intro entry
  exact (DensityOperator.applyUnitary_mul (second entry) (first entry) (state.block entry)).symm

end ExecutionState

namespace Circuit

open Execution

private lemma reference_product {Local Reference : Register}
    (second first : UnitaryOperator Local) :
    UnitaryOperator.prodTensor second (1 : UnitaryOperator Reference) *
        UnitaryOperator.prodTensor first (1 : UnitaryOperator Reference) =
      UnitaryOperator.prodTensor (second * first) (1 : UnitaryOperator Reference) := by
  apply Subtype.ext
  change (UnitaryOperator.prodTensor second (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod Local Reference)) *
    (UnitaryOperator.prodTensor first (1 : UnitaryOperator Reference) :
      HilbertOperator (Register.prod Local Reference)) = _
  rw [unitaryOperator_prodTensor_identity, unitaryOperator_prodTensor_identity,
    unitaryOperator_prodTensor_identity, HilbertOperator.kronecker_identity_mul]
  rfl

variable {gates : GateModel} {oracles : OracleModel} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {ctx : RuntimeCtx .quantum} {allowAllocation : Bool}

/-- Compose already-proved actual component equations on their real intermediate Store. -/
lemma execute_sequenceStoreUnitaryRecord
    (first second : Circuit (.quantum gates oracles operations services) ctx ctx allowAllocation)
    (firstRecord : Store ctx → Store ctx × first.Path)
    (secondRecord : Store ctx → Store ctx × second.Path)
    (firstOperator secondOperator : Store ctx → UnitaryOperator ctx.register)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (firstEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
      first.execute environment Reference state =
        (state.applyUnitary fun entry => UnitaryOperator.prodTensor (firstOperator entry.1)
          (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
            let result := firstRecord entry.1
            (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
      second.execute environment Reference state =
        (state.applyUnitary fun entry => UnitaryOperator.prodTensor (secondOperator entry.1)
          (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
            let result := secondRecord entry.1
            (result.1, (entry.2.1, (entry.2.2, result.2)))))
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (first.seq second).execute environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        (secondOperator (firstRecord entry.1).1 * firstOperator entry.1)
        (1 : UnitaryOperator Reference)).mapClassical (fun entry =>
          let result := sequenceStoreRecord first second firstRecord secondRecord entry.1
          (result.1, (entry.2.1, (entry.2.2, result.2)))) := by
  rw [execute_seq, firstEquation, secondEquation, ExecutionState.applyUnitary_mapClassical,
    ExecutionState.executionState_applyUnitary_comp]
  simp only [reference_product, State.mapHistory,
    ExecutionState.executionState_mapClassical_comp, Function.comp_def]
  exact ExecutionState.executionState_mapClassical_congr _ rfl

end Circuit

end

end QuantumAlg
