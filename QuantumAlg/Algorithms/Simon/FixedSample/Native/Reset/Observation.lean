/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Reset.Support
import all QuantumAlg.Algorithms.Simon.FixedSample.Native.Reset.Store
import all QuantumAlg.Core.Execution.Reference.Weighted

/-!
# Exact complete original-store and reference blocks after reusable reset

Only the raw result cells are overwritten. Every weight on the complete
original store retains its arbitrary reference matrix, and the original
bank is zero in each such block. In particular, the theorem preserves all
caller data and all count packed sample slots simultaneously.
-/

namespace QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {allowAllocation : Bool} {oracles : OracleModel}
  {environment : (nativeModel oracles).Environment}
variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (n count : Nat)

/-- One actual correction retains every old-store-weighted reference entry. -/
lemma selected_reference (half : Fin 2)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History))
    (weight : Store (context base noQuantum n count) → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((selected (allowAllocation := allowAllocation) (oracles := oracles)
        base noQuantum n count half).execute environment Reference state)
      (fun entry _ => weight entry.1) left right =
      ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) left right := by
  rw [show selected (allowAllocation := allowAllocation) (oracles := oracles)
    base noQuantum n count half = Circuit.branch
      (QubitReadouts.input (cells base noQuantum n count))
      (fun value => Circuit.unitary (allowAllocation := allowAllocation)
        (operations := BitWord.model) (classicalOracles := .empty)
        (correction base noQuantum n count half value)) from rfl,
    Circuit.selectedUnitary_execute, ExecutionState.referenceFiberSum_mapClassical]
  exact ExecutionState.referenceFiberSum_applyLocalUnitary state
    (fun entry => (correction base noQuantum n count half
      (entry.1.read (QubitReadouts.input (cells base noQuantum n count)))).matrix
        environment.quantum)
    (fun entry => weight entry.1) left right

/-- One batch preserves every joint reference observation on the entire original store. -/
lemma batch_reference (half : Fin 2)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History))
    (weight : Store (bankContext base noQuantum n count) → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((batch (allowAllocation := allowAllocation) (oracles := oracles)
        base noQuantum n count half).execute environment Reference state)
      (fun entry _ => weight (originalStore base noQuantum n count entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (originalStore base noQuantum n count entry.1)) left right := by
  change ExecutionState.referenceFiberSum
    ((Circuit.seq (measure (allowAllocation := allowAllocation) base noQuantum n count half)
      (selected (allowAllocation := allowAllocation) base noQuantum n count half)).execute
        environment
        Reference state) _ left right = _
  rw [Circuit.execute_seq (environment := environment)]
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
  refine (selected_reference (allowAllocation := allowAllocation) (oracles := oracles)
    base noQuantum n count half
    ((measure (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count half).execute environment Reference state)
    (fun store => weight (originalStore base noQuantum n count store)) left right).trans ?_
  change ExecutionState.referenceFiberSum
    ((Circuit.measurementSequence (allowAllocation := allowAllocation)
      (gates := AlgorithmGate.model) (oracles := oracles)
      (operations := BitWord.model) (classicalOracles := .empty)
      (readouts base noQuantum n count half)).execute environment Reference state) _ _ _ = _
  rw [Circuit.measurementSequence_referenceFiberSum]
  change ExecutionState.referenceFiberSum state
    (fun entry basis => weight (originalStore base noQuantum n count
      (writtenStore (allowAllocation := allowAllocation) (oracles := oracles)
        base noQuantum n count half entry.1 basis))) _ _ = _
  simp only [originalStore_written]

/-- The two real batches retain the complete original classical store and reference observation.
-/
lemma code_reference {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History))
    (weight : Store (bankContext base noQuantum n count) → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code (allowAllocation := allowAllocation) (oracles := oracles)
        base noQuantum n count).execute environment Reference state)
      (fun entry _ => weight (originalStore base noQuantum n count entry.1)) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (originalStore base noQuantum n count entry.1)) left right := by
  change ExecutionState.referenceFiberSum
    ((Circuit.seq (batch (allowAllocation := allowAllocation) base noQuantum n count 0)
      (batch (allowAllocation := allowAllocation) base noQuantum n count 1)).execute environment
        Reference state) _ left right = _
  rw [Circuit.execute_seq (environment := environment)]
  simp only [State.mapHistory, ExecutionState.referenceFiberSum_mapClassical]
  rw [batch_reference (allowAllocation := allowAllocation) (oracles := oracles)
    base noQuantum n count 1]
  exact batch_reference (allowAllocation := allowAllocation) (oracles := oracles)
    base noQuantum n count 0 state weight left right

/-- Every complete untouched-store block has the zero bank and its entire input reference fiber.
-/
lemma code_originalStore_entry {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum n count) Reference (Unit × History))
    (stored : Store (bankContext base noQuantum n count))
    (left right : (context base noQuantum n count).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((code (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count).execute environment Reference state).mapClassical
      (fun entry => originalStore base noQuantum n count entry.1)).block stored).matrix
        (left, leftRef) (right, rightRef) =
      if left = (context base noQuantum n count).quantumLayout.zeroLabel ∧
        right = (context base noQuantum n count).quantumLayout.zeroLabel then
        ExecutionState.referenceFiberSum state
          (fun entry _ => if originalStore base noQuantum n count entry.1 = stored then 1 else 0)
          leftRef rightRef
      else 0 := by
  rw [BasisSeeded.readout_entry _ _
    (code_seeded (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count state)]
  exact congrArg
    (fun value : ℂ => if left = (context base noQuantum n count).quantumLayout.zeroLabel ∧
      right = (context base noQuantum n count).quantumLayout.zeroLabel then value else 0)
    (code_reference (allowAllocation := allowAllocation) (oracles := oracles)
      base noQuantum n count state (fun original => if original = stored then 1 else 0)
      leftRef rightRef)

end

end QuantumAlg.SimonsProblem.FixedSample.Native.ReusedReset
