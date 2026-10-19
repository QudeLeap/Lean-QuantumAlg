/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Scope.Semantics
import all QuantumAlg.Primitives.ZReset.Frame
import all QuantumAlg.Core.Execution.Unitary.Local
import all QuantumAlg.Core.Execution.Reference.Unitary

/-!
# Actual bank reset followed by an actual basis reload

The single execution first measures and corrects the existing bank through
the scoped reset program, then applies the specified placed unitary circuit.
When that actual circuit maps the zero label to a given basis seed, each
complete classical store retains its entire reference operator and the bank
has exactly that seed. The initial state may have arbitrary correlations.

The seed equation is a mathematical premise about the supplied gate program,
separate from the code and discharged by its real basis action. Neither the
state nor a resource witness is supplied as a substitute for execution.
Reset does not restore borrowed quantum systems; an algorithm must provide
its owned bank and separately prove its mandatory borrowed contract.
-/

namespace QuantumAlg.ZReset.Reload

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {environment : (ExecutionModel.quantum AlgorithmGate.model oracles).Environment}

/-- Execute the real scoped reset and then the real placed reload gate sequence. -/
def code (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
    (reload : UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout) :
    Circuit (.quantum AlgorithmGate.model oracles) ctx ctx :=
  .seq (BankScope.code (oracles := oracles) qubits) (.unitary reload)

private lemma local_basis_block {R Reference : Register} (program : UnitaryOperator R)
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

private lemma reload_column
    (reload : UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout)
    (seed : ctx.register.Index)
    (action : reload.applyNormalized environment.quantum
      (NormalizedVector.ket (R := ctx.register) ctx.quantumLayout.zeroLabel) =
        NormalizedVector.ket (R := ctx.register) seed) (row : ctx.register.Index) :
    (reload.matrix environment.quantum) row ctx.quantumLayout.zeroLabel =
      NormalizedVector.ket (R := ctx.register) seed row := by
  have actual := congrArg (fun vector : NormalizedVector ctx.register => vector row) action
  change reload.applyVec environment.quantum
    (NormalizedVector.ket (R := ctx.register) ctx.quantumLayout.zeroLabel).vec row = _ at actual
  rw [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at actual
  exact actual

/-- Every complete actual classical store keeps its reference block and receives the exact seed. -/
lemma zResetReload_store_entry
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    (reload : UnitaryCircuit AlgorithmGate.model oracles ctx.quantumLayout)
    (seed : ctx.register.Index)
    (action : reload.applyNormalized environment.quantum
      (NormalizedVector.ket (R := ctx.register) ctx.quantumLayout.zeroLabel) =
        NormalizedVector.ket (R := ctx.register) seed)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState × History))
    (original : Store ctx)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical
      ((code qubits reload).execute environment Reference state)
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      NormalizedVector.ket (R := ctx.register) seed left *
        (∑ basis : ctx.register.Index,
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)) *
        star (NormalizedVector.ket (R := ctx.register) seed right) := by
  let reset := BankScope.code (oracles := oracles) qubits
  let reloadCode : Circuit (.quantum AlgorithmGate.model oracles) ctx ctx :=
    .unitary reload
  let predicate := fun store : Store ctx => store = original
  let resetState := reset.execute environment Reference state
  let reloaded := reloadCode.execute environment Reference resetState
  let reassociate := fun history :
      (ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState ×
        ((History × reset.Path) × reloadCode.Path) =>
    (history.1, (history.2.1.1, (history.2.1.2, history.2.2)))
  have executed := congrArg
    (fun output : State ctx Reference
      ((ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState ×
        (History × (Circuit.seq reset reloadCode).Path)) =>
      (output.filterClassical (fun entry => predicate entry.1)).quantumMarginal)
    (Circuit.execute_seq (environment := environment) reset reloadCode state)
  have history := congrArg ExecutionState.quantumMarginal
    (ZReset.filter_mapHistory (ctx := ctx) (Reference := Reference)
      (History := (ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState ×
        ((History × reset.Path) × reloadCode.Path))
      (Later := (ExecutionModel.quantum AlgorithmGate.model oracles).HiddenState ×
        (History × (reset.Path × reloadCode.Path)))
      reloaded reassociate predicate)
  have erased := State.mapHistory_quantumMarginal
    (reloaded.filterClassical (fun entry => predicate entry.1)) reassociate
  have filtered := congrArg ExecutionState.quantumMarginal
    (ZReset.filter_unitary (environment := environment)
      (allowAllocation := true) resetState reload predicate)
  have acted := Circuit.unitary_jointDensity (allowAllocation := true)
    (operations := .empty)
    (services := .empty) environment reload
    (resetState.filterClassical (fun entry => predicate entry.1))
  have composed := executed.trans (history.trans (erased.trans (filtered.trans acted)))
  refine (congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      density.matrix (left, leftRef) (right, rightRef)) composed).trans ?_
  refine (local_basis_block (reload.matrix environment.quantum) _ ctx.quantumLayout.zeroLabel
    left right leftRef rightRef _
    (fun row column => BankScope.zResetBankScope_complete_store_entry
      qubits state original row column leftRef rightRef)).trans ?_
  exact congrArg₂ (fun first second : ℂ => first *
    (∑ basis : ctx.register.Index,
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (basis, leftRef) (basis, rightRef)) * star second)
    (reload_column reload seed action left) (reload_column reload seed action right)

end

end QuantumAlg.ZReset.Reload
