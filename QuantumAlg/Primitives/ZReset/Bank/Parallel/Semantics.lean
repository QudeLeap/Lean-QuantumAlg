/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Body.Observed
import all QuantumAlg.Primitives.ZReset.Bank.Parallel.Workspace.Semantics

/-!
# Complete original-store and reference preservation by parallel bank reset

The parent allocates one real scalar outcome cell per physical bank wire.
Actual Z writes select the one native parallel X layer, and scope exit
removes precisely those fresh cells. Every complete original-store block
retains its full reference matrix while the complete bank becomes zero.
The input may be any mixed, entangled, or subnormalized state.
-/

namespace QuantumAlg.ZReset.BankParallel

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {oracles : OracleModel}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

variable {environment : (ExecutionModel.quantum AlgorithmGate.model
  oracles operations services).Environment}

/-- The actual complete parent preserves every predicate on its entire original store. -/
lemma code_resetEquation
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    (predicate : Store ctx → Prop) :
    ResetEquation environment (code (oracles := oracles) qubits operations services) predicate := by
  by_cases empty : ctx.systemCount = 0
  · rw [code_zero qubits empty]
    exact identity_resetEquation_empty empty predicate
  · rw [code, if_neg empty]
    apply Workspace.scope_resetEquation
    intro Reference History historyFinite state left right leftRef rightRef
    apply body_observed_entry
      (Workspace.wireEquiv ctx ctx.systemCount) (work_qubits qubits)
      (Workspace.reference ctx ctx.systemCount)
      (Workspace.reference_key_injective ctx ctx.systemCount)
      (fun store => predicate (Workspace.forgetStore ctx ctx.systemCount store))
      _ state left right leftRef rightRef
    intro store basis
    refine writtenStore_predicate (allowAllocation := true) (oracles := oracles)
      (operations := operations) (services := services)
      (Workspace.wireEquiv ctx ctx.systemCount) (work_qubits qubits)
      (Workspace.reference ctx ctx.systemCount)
      (fun original => predicate (Workspace.forgetStore ctx ctx.systemCount original))
      ?_ store basis
    intro item present original value
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
    exact Iff.of_eq (congrArg predicate
      (Workspace.forgetStore_write ctx.systemCount _
        ⟨index, QubitReadouts.readout_key _ _ _⟩ original value))

/-- The complete original store and its arbitrary reference block survive the one-layer reset. -/
lemma code_complete_store_entry
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (original : Store ctx)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    (((code (oracles := oracles) qubits operations services).execute environment Reference
      state).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index,
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)
      else 0 :=
  code_resetEquation qubits (fun store => store = original)
    Reference state left right leftRef rightRef

private lemma filter_true {C : Type} [Fintype C] {R : Register}
    (decision : DecidablePred (fun _ : C => True)) (state : ExecutionState C R) :
    (@ExecutionState.filterClassical C _ R state (fun _ => True) decision) = state := by
  apply ExecutionState.ext
  intro value
  simp only [ExecutionState.filterClassical_block, if_true]

/-- Summing original stores retains the entire incoming reference marginal at the zero bank. -/
lemma code_complete_entry
    (qubits : ∀ wire : Fin ctx.systemCount, (ctx.quantumLayout.wire wire).dimension = 2)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    ((code (oracles := oracles) qubits operations services).execute environment Reference
      state).quantumMarginal.matrix
      (left, leftRef) (right, rightRef) =
      if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
        ∑ basis : ctx.register.Index, state.quantumMarginal.matrix
          (basis, leftRef) (basis, rightRef)
      else 0 := by
  simpa only [filter_true] using
    code_resetEquation (oracles := oracles) (operations := operations) (services := services)
      qubits (fun _ => True) Reference state left right leftRef rightRef

end

end QuantumAlg.ZReset.BankParallel
