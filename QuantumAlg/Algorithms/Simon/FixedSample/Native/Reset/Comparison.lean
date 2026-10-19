/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Reset.Observation
import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Reset.Sample
import all QuantumAlg.Primitives.ZReset.Bank.Scope.Semantics
import all QuantumAlg.Core.Execution.Basis.Seeded.Observation

/-!
# Complete protocol equivalence with scoped serial bank reset

The reusable implementation and scoped serial bank reset first agree on the
entire original-store observation and the full joint bank/reference state.
The following real sample overwrites every raw cell, yielding equality on
the complete final Store and joint quantum state. Only execution histories
are forgotten; no output storage or quantum system is removed.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {oracles : OracleModel}
  {environment : (nativeModel oracles).Environment}
variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

private lemma scoped_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History)) :
    BasisSeeded.Holds (context base noQuantum n count).quantumLayout.zeroLabel
      ((ZReset.BankScope.code (oracles := oracles)
        (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count))
        BitWord.model).execute environment Reference state) := by
  intro stored left right leftRef rightRef
  have seed := ZReset.BankScope.zResetBankScope_complete_store_entry_operationModel
    (environment := ⟨environment.quantum, environment.classical⟩)
    (services := .empty) (oracles := oracles)
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count))
    BitWord.model state stored (context base noQuantum n count).quantumLayout.zeroLabel
    (context base noQuantum n count).quantumLayout.zeroLabel leftRef rightRef
  simp only [and_self, if_true] at seed
  exact (ZReset.BankScope.zResetBankScope_complete_store_entry_operationModel
    (environment := ⟨environment.quantum, environment.classical⟩)
    (services := .empty) (oracles := oracles)
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count))
    BitWord.model state stored left right leftRef rightRef).trans
    (congrArg (fun coefficient => if left = (context base noQuantum n count).quantumLayout.zeroLabel
      ∧ right = (context base noQuantum n count).quantumLayout.zeroLabel then coefficient else 0)
      seed.symm)

private lemma scoped_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History))
    (weight : Store (context base noQuantum n count) → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((ZReset.BankScope.code (oracles := oracles)
        (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count))
        BitWord.model).execute environment Reference state)
      (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) left right := by
  refine (BasisSeeded.referenceFiberSum_seed _ _
    (scoped_seeded (oracles := oracles) base noQuantum n count state) weight left right).trans ?_
  refine Eq.trans ?_ (BasisSeeded.fiber_store_blocks state
    (fun original _ => weight original) left right).symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [← Finset.mul_sum]
  apply congrArg (fun coefficient : ℂ => weight original * coefficient)
  have actual := ZReset.BankScope.zResetBankScope_complete_store_entry_operationModel
    (environment := ⟨environment.quantum, environment.classical⟩)
    (services := .empty) (oracles := oracles)
    (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count))
    BitWord.model state original (context base noQuantum n count).quantumLayout.zeroLabel
    (context base noQuantum n count).quantumLayout.zeroLabel left right
  simp only [and_self, if_true] at actual
  convert actual using 1
  congr 1

/-- Both reset implementations agree on all untouched classical cells and the complete joint state.
-/
lemma code_originalStore_eq_scoped {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History)) :
    ((code (allowAllocation := true) (oracles := oracles)
      base noQuantum n count).execute environment Reference state).mapClassical
      (fun entry => originalStore base noQuantum n count entry.1) =
      ((ZReset.BankScope.code (oracles := oracles)
        (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count))
        BitWord.model).execute environment Reference state).mapClassical
        (fun entry => originalStore base noQuantum n count entry.1) := by
  apply ExecutionState.ext
  intro stored
  apply DensityOperator.ext
  funext left right
  obtain ⟨left, leftRef⟩ := left
  obtain ⟨right, rightRef⟩ := right
  rw [code_originalStore_entry, BasisSeeded.readout_entry _ _
    (scoped_seeded (oracles := oracles) base noQuantum n count state)]
  exact (congrArg
    (fun value : ℂ => if left = (context base noQuantum n count).quantumLayout.zeroLabel ∧
      right = (context base noQuantum n count).quantumLayout.zeroLabel then value else 0)
    (scoped_reference (oracles := oracles) base noQuantum n count state
      (fun original => if originalStore base noQuantum n count original = stored then 1 else 0)
      leftRef rightRef)).symm

/-- Reset followed by the entire real sample preserves every final store, bank and reference block.
-/
lemma code_sample_eq_scoped (sampling : SamplingCircuit n)
    {environment : (executionModel n).Environment} (index : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History)) :
    (((code (allowAllocation := true) (oracles := sourceModel n)
      base noQuantum n count).seq
      (sample base noQuantum n count sampling index)).execute environment
        Reference state).mapClassical
      (fun entry => entry.1) =
      (((ZReset.BankScope.code (oracles := sourceModel n)
        (nativeSimon_context_qubits n (nativeSimon_context_wires base noQuantum n count))
        BitWord.model).seq (sample base noQuantum n count sampling index)).execute environment
          Reference state).mapClassical (fun entry => entry.1) := by
  rw [sequence_store (environment := environment), sequence_store (environment := environment)]
  exact sample_congr_originalStore
    (environment := environment) base noQuantum n count sampling index _ _
    (code_originalStore_eq_scoped base noQuantum n count state)

end

end QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset
