/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Scope.Semantics
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation

/-!
# Reusable observations of the actual scoped bank reset

The real scratch-scoped reset makes the full physical bank zero in each
complete store-reference block and preserves all store-weighted reference
observations. These are consequences of its existing execution semantics.
-/

namespace QuantumAlg.ZReset.BankScope

open Execution

noncomputable section

variable {services : ClassicalOracleModel}

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {environment : (ExecutionModel.quantum AlgorithmGate.model oracles .empty services).Environment}
  (qubits : ∀ wire : Fin ctx.systemCount,
    (ctx.quantumLayout.wire wire).dimension = 2)
  {Reference : Register} {History : Type} [Fintype History]
  (state : State ctx Reference
    ((ExecutionModel.quantum AlgorithmGate.model oracles .empty services).HiddenState × History))

/-- The paid reset establishes physical zero without an incoming seed premise. -/
lemma seeded :
    BasisSeeded.Holds ctx.quantumLayout.zeroLabel
      ((code (services := services) (oracles := oracles) qubits).execute
        ⟨environment.quantum, environment.classical⟩ Reference state) := by
  intro original left right leftRef rightRef
  have zero := zResetBankScope_complete_store_entry (environment := environment)
    (oracles := oracles) qubits state original
    ctx.quantumLayout.zeroLabel ctx.quantumLayout.zeroLabel leftRef rightRef
  simp only [and_self] at zero
  exact (zResetBankScope_complete_store_entry
    (oracles := oracles) qubits state original left right leftRef rightRef).trans
      (congrArg (fun coefficient : ℂ =>
        if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
          coefficient else 0) zero.symm)

/-- Every complete original store's reference weight survives the paid reset. -/
lemma referenceFiberSum_preserved (weight : Store ctx → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code (services := services) (oracles := oracles) qubits).execute
        ⟨environment.quantum, environment.classical⟩ Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight entry.1) leftRef rightRef := by
  refine (BasisSeeded.referenceFiberSum_seed ctx.quantumLayout.zeroLabel _
    (seeded qubits state) weight leftRef rightRef).trans ?_
  refine Eq.trans ?_ (BasisSeeded.fiber_store_blocks state
    (fun original _ => weight original) leftRef rightRef).symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [← Finset.mul_sum]
  apply congrArg (fun coefficient : ℂ => weight original * coefficient)
  simpa only [and_self, if_true] using
    zResetBankScope_complete_store_entry (oracles := oracles) qubits state original
      ctx.quantumLayout.zeroLabel ctx.quantumLayout.zeroLabel leftRef rightRef

end

end QuantumAlg.ZReset.BankScope
