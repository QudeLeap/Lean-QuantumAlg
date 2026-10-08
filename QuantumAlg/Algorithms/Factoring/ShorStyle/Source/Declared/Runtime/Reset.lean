/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Placement
import all QuantumAlg.Primitives.ZReset.Bank.Scope.Semantics
import all QuantumAlg.Primitives.ZReset.Bank.Scope.Observation
import all QuantumAlg.Primitives.ZReset.Bank.Scope.OperationModel

/-!
# Paid physical reset of the same declared Shor bank

The native measurement-and-X sequence uses one actual lexical scratch cell.
It neither prepares nor replaces a quantum system. Every complete original
store-reference block survives, while the unchanged bank becomes zero.
Restoration of borrowed quantum systems requires a separate ownership proof.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (ctx : RuntimeCtx .quantum) (N : Nat) (input : Input N)
  (sameWires : ctx.quantumWires = (layout N).wires)

/-- Reset the original physical bank with one real scoped result cell. -/
def reset : Circuit (executionModel input) ctx ctx :=
  ZReset.BankScope.code (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (shorDeclared_context_qubits N sameWires) BitWord.model

include sameWires in
/-- Actual corresponding wire positions determine the complete physical width. -/
theorem reset_bank_systemCount : ctx.systemCount = bankQubits N := by
  have same := Fintype.card_congr (wireEquiv N sameWires)
  simpa only [Fintype.card_fin] using same.symm

/-- The actual reset establishes zero on each complete original store-reference block. -/
theorem reset_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History)) :
    BasisSeeded.Holds ctx.quantumLayout.zeroLabel
      ((reset ctx N input sameWires).execute Reference state) := by
  intro original left right leftRef rightRef
  have zero := ZReset.BankScope.zResetBankScope_complete_store_entry_operationModel
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (shorDeclared_context_qubits N sameWires) BitWord.model state original
    ctx.quantumLayout.zeroLabel ctx.quantumLayout.zeroLabel leftRef rightRef
  simp only [and_self] at zero
  exact (ZReset.BankScope.zResetBankScope_complete_store_entry_operationModel
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (shorDeclared_context_qubits N sameWires) BitWord.model state original
    left right leftRef rightRef).trans
      (congrArg (fun coefficient : ℂ =>
        if left = ctx.quantumLayout.zeroLabel ∧ right = ctx.quantumLayout.zeroLabel then
          coefficient else 0) zero.symm)

/-- Reset preserves every weight of the complete original store and arbitrary reference. -/
theorem reset_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference ((executionModel input).HiddenState × History))
    (weight : Store ctx → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((reset ctx N input sameWires).execute Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight entry.1) leftRef rightRef :=
  (ZReset.BankScope.referenceFiberSum_operationModel
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (shorDeclared_context_qubits N sameWires) BitWord.model state weight leftRef rightRef).trans
      (ZReset.BankScope.referenceFiberSum_preserved
        (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
        (shorDeclared_context_qubits N sameWires) state weight leftRef rightRef)

/-- Each actual path pays one measurement and at most one native X per bank wire. -/
theorem reset_events_le (path : (reset ctx N input sameWires).Path) :
    (reset ctx N input sameWires).resourcePool path ≤
      ZReset.Bank.envelope
        (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
        (bankQubits N) BitWord.model := by
  have paid := ZReset.BankScope.zResetBankScope_resourcePool_le
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (operations := BitWord.model) (shorDeclared_context_qubits N sameWires) path
  rw [reset_bank_systemCount ctx N sameWires] at paid
  exact paid

/-- The same actual serial reset has depth at most twice the complete bank width. -/
theorem reset_depth_le (path : (reset ctx N input sameWires).Path) :
    (reset ctx N input sameWires).depth (fun _ => 1) path ≤ 2 * bankQubits N := by
  have paid := ZReset.BankScope.zResetBankScope_unitDepth_le
    (oracles := DeclaredSource.model (sourceBounds input) (phaseBits N))
    (operations := BitWord.model) (shorDeclared_context_qubits N sameWires) path
  rw [reset_bank_systemCount ctx N sameWires] at paid
  exact paid

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
