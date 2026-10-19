/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Primitives.ZReset.Frame
import all QuantumAlg.Core.Execution.Selected.Unitary

/-!
# Actual stored-parameter dispatch on every classical-reference block

The real branch instruction reads the retained parameter before executing
its compiled unitary member. It preserves every predicate on the complete
classical store, and each resulting quantum block is conjugated by the member
selected by that store. All equations retain an arbitrary external reference
and do not assume that it is independent of the parameter or quantum bank.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- Every actual store predicate commutes with stored-parameter unitary dispatch. -/
lemma shortDLP_runtimeSelected_filter {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ) (predicate : Store ctx → Prop)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    ExecutionState.filterClassical
      ((selected m ell width sameWires parameter N generator target).execute
        environment Reference state)
      (fun entry => predicate entry.1) =
      (selected m ell width sameWires parameter N generator target).execute environment Reference
        (state.filterClassical (fun entry => predicate entry.1)) :=
  ZReset.filter_branch (environment := environment) (model := model) (ctx := ctx) parameter
    (fun value => .unitary (operations := BitWord.model) (classicalOracles := .empty)
      (RuntimePlacement.memberProgram m ell width sameWires N
        (generator value) (target value))) predicate
    (by
      intro value reference history finite part
      simp only [Circuit.execute_unitary, ZReset.filter_map, ZReset.filter_applyUnitary]
      exact ExecutionState.executionState_mapClassical_congr_decision
        _ _ _ (fun _ => rfl) _ _)
    Reference state

/-- Each selected store-reference block uses the member read from its actual original store. -/
lemma shortDLP_runtimeSelected_joint_matrix {shape : CShape} (parameter : CInputRef ctx shape)
    (N : Nat) (generator target : shape.Value → (ZMod N)ˣ) (predicate : Store ctx → Prop)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (ExecutionState.filterClassical
      ((selected m ell width sameWires parameter N generator target).execute
        environment Reference state)
      (fun entry => predicate entry.1)).quantumMarginal.matrix =
      ∑ entry : Store ctx × (model.HiddenState × History),
        (DensityOperator.applyUnitary
          (UnitaryOperator.prodTensor
            ((RuntimePlacement.memberProgram m ell width sameWires N
              (generator (entry.1.read parameter)) (target (entry.1.read parameter))).matrix
                environment.quantum)
            (1 : UnitaryOperator Reference))
          ((state.filterClassical (fun source => predicate source.1)).block entry)).matrix :=
  (congrArg (fun result : State ctx Reference
      (model.HiddenState ×
        (History × (selected m ell width sameWires parameter N generator target).Path)) =>
        result.quantumMarginal.matrix)
    (shortDLP_runtimeSelected_filter m ell width sameWires parameter N generator target
      predicate Reference state)).trans
    (Circuit.circuit_selectedUnitary_quantumMarginal_matrix (environment := environment)
      (operations := BitWord.model) (classicalOracles := .empty) parameter
      (fun value => RuntimePlacement.memberProgram m ell width sameWires N
        (generator value) (target value))
      (state.filterClassical (fun entry => predicate entry.1)))

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
