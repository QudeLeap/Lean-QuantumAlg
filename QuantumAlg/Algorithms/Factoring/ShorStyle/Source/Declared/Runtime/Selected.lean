/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Born
import all QuantumAlg.Core.Execution.Basis.Seeded.Allocation
import all QuantumAlg.Core.Execution.Selected.Store

/-!
# Full stored-base selection on the declared Shor bank

The selected member acts on each original complete store, hidden state and
history. Its actual branch path records precisely the stored parameter read.
The full operator is tensored with identity on every external reference.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable (base : RuntimeCtx .quantum) (N : Nat) (input : Input N)
  (sameWires : base.quantumWires = (layout N).wires)

variable {environment : (executionModel N).Environment}

/-- The actual stored-value branch preserves the entire old record and reference operator. -/
lemma selected_execute (parameter : CInputRef base (ParameterShape (modulusBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Storage.context base N) Reference
      ((executionModel N).HiddenState × History)) :
    (selected base N sameWires parameter).execute environment Reference state =
      (state.applyUnitary fun entry => UnitaryOperator.prodTensor
        ((member N ((Storage.quantumWires base N).trans sameWires)
          (entry.1.read (Storage.liftInput base N parameter))).matrix environment.quantum)
        (1 : UnitaryOperator Reference)).mapClassical
          (fun entry => (entry.1, (entry.2.1,
            (entry.2.2, ⟨entry.1.read (Storage.liftInput base N parameter), ()⟩)))) :=
  Circuit.selectedUnitary_execute _ _ environment state

/-- A complete store chooses its own granted member, preserving its full reference matrix. -/
lemma selected_store_matrix (parameter : CInputRef base (ParameterShape (modulusBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Storage.context base N) Reference
      ((executionModel N).HiddenState × History))
    (original : Store (Storage.context base N)) :
    (((selected base N sameWires parameter).execute environment Reference state).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix =
      (DensityOperator.applyUnitary (UnitaryOperator.prodTensor
        ((member N ((Storage.quantumWires base N).trans sameWires)
          (original.read (Storage.liftInput base N parameter))).matrix environment.quantum)
        (1 : UnitaryOperator Reference))
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal).matrix :=
  Circuit.selectedUnitary_store_matrix _ _ environment state original

/-- Every original complete store has the actual source vector and its own reference block. -/
lemma selected_seed_entry (parameter : CInputRef base (ParameterShape (modulusBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Storage.context base N) Reference
      ((executionModel N).HiddenState × History))
    (seeded : BasisSeeded.Holds (Storage.context base N).quantumLayout.zeroLabel state)
    (original : Store (Storage.context base N))
    (left right : (Storage.context base N).register.Index)
    (leftRef rightRef : Reference.Index) :
    (((selected base N sameWires parameter).execute
      (Runtime.environment input) Reference state).filterClassical
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      (DeclaredSource.evolvedState (sourceBounds input) (phaseBits N)
        (selectedBase (original.read (Storage.liftInput base N parameter)))).normalized
          (basisEquiv N ((Storage.quantumWires base N).trans sameWires) left) *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          ((Storage.context base N).quantumLayout.zeroLabel, leftRef)
          ((Storage.context base N).quantumLayout.zeroLabel, rightRef) *
        star ((DeclaredSource.evolvedState (sourceBounds input) (phaseBits N)
          (selectedBase (original.read (Storage.liftInput base N parameter)))).normalized
            (basisEquiv N ((Storage.quantumWires base N).trans sameWires) right)) := by
  rw [selected_store_matrix]
  refine (BasisSeeded.unitary_entry (Storage.context base N).quantumLayout.zeroLabel
    state seeded
    ((member N ((Storage.quantumWires base N).trans sameWires)
      (original.read (Storage.liftInput base N parameter))).matrix
        (Runtime.environment input).quantum)
    original left right leftRef rightRef).trans ?_
  rw [member_zero_amplitude, member_zero_amplitude]

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
