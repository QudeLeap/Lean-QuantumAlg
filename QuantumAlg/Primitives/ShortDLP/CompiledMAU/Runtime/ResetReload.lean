/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed
import all QuantumAlg.Primitives.ZReset.Bank.Scope.Semantics
import all QuantumAlg.Primitives.ZReset.Frame
import all QuantumAlg.Core.Execution.Unitary.StoreFilter
import all QuantumAlg.Core.Execution.Reference.Unitary

/-!
# Exact reusable seed after actual scoped reset and literal reload

The reset's complete store-reference blocks are followed by the actual
placed X reload. The resulting local state is exactly the source seed, while
each complete classical store retains its entire reference operator. This
proves restoration of the seed without assuming independence beforehand.

The operation resets the complete bank identified by the internal layout
equality. Its surrounding factoring construction supplies that owned bank;
this component does not claim restoration of arbitrary borrowed quantum
systems which a different caller might have included in the reset layout.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private theorem local_basis_block {R Reference : Register} (program : UnitaryOperator R)
    (state : DensityOperator (Register.prod R Reference)) (zero : R.Index)
    (left right : R.Index) (leftRef rightRef : Reference.Index) (coefficient : ℂ)
    (atZero : ∀ row column,
      state.matrix (row, leftRef) (column, rightRef) =
        if row = zero ∧ column = zero then coefficient else 0) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor program (1 : UnitaryOperator Reference)) state).matrix
        (left, leftRef) (right, rightRef) =
      program left zero * coefficient * star (program right zero) := by
  rw [DensityOperator.localUnitary_block]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply, atZero,
    ite_and, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

private theorem reload_column (N : Nat) (row : ctx.register.Index) :
    (RuntimePlacement.reloadProgram m ell width sameWires N).matrix
        row ctx.quantumLayout.zeroLabel =
      NormalizedVector.ket (R := ctx.register)
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (CompiledMAU.reloadLabel m ell width N)) row := by
  have action := congrArg (fun vector : NormalizedVector ctx.register => vector row)
    (RuntimePlacement.shortDLP_runtimeReload_apply_zero m ell width sameWires N)
  change (RuntimePlacement.reloadProgram m ell width sameWires N).applyVec
    (NormalizedVector.ket (R := ctx.register) ctx.quantumLayout.zeroLabel).vec row = _ at action
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at action
  exact action

/-- Each actual complete store-reference block ends with the original source seed exactly. -/
theorem shortDLP_runtimeResetReload_store_entry (N : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) (original : Store ctx)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical
      ((resetReload m ell width sameWires N).execute Reference state)
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      NormalizedVector.ket (R := ctx.register)
          ((RuntimePlacement.basisEquiv m ell width sameWires).symm
            (CompiledMAU.reloadLabel m ell width N)) left *
        (∑ basis : ctx.register.Index,
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)) *
        star (NormalizedVector.ket (R := ctx.register)
          ((RuntimePlacement.basisEquiv m ell width sameWires).symm
            (CompiledMAU.reloadLabel m ell width N)) right) := by
  let reset : Circuit model ctx ctx := ZReset.BankScope.code
    (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires) BitWord.model
  let reload : Circuit model ctx ctx :=
    .unitary (RuntimePlacement.reloadProgram m ell width sameWires N)
  let predicate := fun store : Store ctx => store = original
  let resetState := reset.execute Reference state
  let reloaded := reload.execute Reference resetState
  let reassociate := fun history : model.HiddenState × ((History × reset.Path) × reload.Path) =>
    (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))
  have executed := congrArg
    (fun output : State ctx Reference
      (model.HiddenState × (History × (Circuit.seq reset reload).Path)) =>
      (output.filterClassical (fun entry => predicate entry.1)).quantumMarginal)
    (Circuit.execute_seq reset reload state)
  have history := congrArg ExecutionState.quantumMarginal
    (ZReset.filter_mapHistory (ctx := ctx) (Reference := Reference)
      (History := model.HiddenState × ((History × reset.Path) × reload.Path))
      (Later := model.HiddenState × (History × (reset.Path × reload.Path)))
      reloaded reassociate predicate)
  have erased := State.mapHistory_quantumMarginal
    (reloaded.filterClassical (fun entry => predicate entry.1)) reassociate
  have acted := Circuit.unitary_store_filter (operations := BitWord.model) (services := .empty)
    (RuntimePlacement.reloadProgram m ell width sameWires N)
    resetState predicate
  have composed := executed.trans (history.trans (erased.trans acted))
  refine (congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      density.matrix (left, leftRef) (right, rightRef)) composed).trans ?_
  refine (local_basis_block
    (RuntimePlacement.reloadProgram m ell width sameWires N).matrix _
    ctx.quantumLayout.zeroLabel left right leftRef rightRef _
    (fun row column => ZReset.BankScope.zResetBankScope_complete_store_entry_operationModel
      (oracles := .empty)
      (RuntimePlacement.shortDLP_runtimePlacement_qubits m ell width sameWires)
      BitWord.model state original row column leftRef rightRef)).trans ?_
  exact congrArg₂ (fun first second : ℂ => first *
    (∑ basis : ctx.register.Index,
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (basis, leftRef) (basis, rightRef)) * star second)
    (reload_column m ell width sameWires N left) (reload_column m ell width sameWires N right)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
