/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Construction
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ZReset.Semantics
import all QuantumAlg.Primitives.ZReset.Circuit.OperationModel
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Semantics

/-!
# Each actual observed control reset preserves the complete joint matrix

These facts reuse the existing measured
reset theorem. They quantify over arbitrary mixed states, caller stores,
references and histories, not only the source seed. No second measurement or
new classical workspace is introduced. The output result remains in its
actual retained cell and each resulting quantum block has control label zero.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling

noncomputable section

open Execution

variable {environment : model.Environment}

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

private def realizations :=
  QuditShift.qubitRealizations (Context base noQuantum m ell width).quantumLayout
    (control base noQuantum m ell width) (control_qubit base noQuantum m ell width) .empty

/-- This is the actual complete store and path record of the one measured correction. -/
def resetRecord (result : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    {History : Type}
    (entry : Store (Context base noQuantum m ell width) × (model.HiddenState × History))
    (outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension) :
    Store (Context base noQuantum m ell width) ×
      (model.HiddenState ×
        (History × (measuredReset base noQuantum m ell width result).Path)) :=
  QuditShift.resetCircuitRecord (allowAllocation := true) (services := .empty)
    (control base noQuantum m ell width)
    (dimensionedCell base noQuantum m ell width result)
    (realizations base noQuantum m ell width) entry outcome

/-- The exact instrument keeps every written store value, history and reference index.
Only the measured outcome's own complete record selects its source matrix block. -/
lemma measuredReset_block_entry
    (result : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (entry : Store (Context base noQuantum m ell width) ×
      (model.HiddenState ×
        (History × (measuredReset base noQuantum m ell width result).Path)))
    (left right : (Context base noQuantum m ell width).quantumLayout.Basis)
    (leftRef rightRef : Reference.Index) :
    (((measuredReset base noQuantum m ell width result).execute environment Reference state).block
        entry).matrix (left, leftRef) (right, rightRef) =
      ∑ source : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
        ∑ outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
            (control base noQuantum m ell width)).dimension,
          if resetRecord base noQuantum m ell width result source outcome = entry then
            if left (control base noQuantum m ell width) = 0 ∧
                right (control base noQuantum m ell width) = 0 then
              (state.block source).matrix
                (Function.update left (control base noQuantum m ell width) outcome, leftRef)
                (Function.update right (control base noQuantum m ell width) outcome, rightRef)
            else 0
          else 0 := by
  exact QuditShift.resetCircuit_block_entry
    (environment := ⟨environment.quantum, environment.classical⟩) (allowAllocation := true)
      (services := .empty)
    (control base noQuantum m ell width) (dimensionedCell base noQuantum m ell width result)
    (realizations base noQuantum m ell width) state entry left right leftRef rightRef

/-- The measured reset retains the exact matrix of the other wires and reference, summing
the physical measurement outcomes once, and places the control at zero. -/
lemma measuredReset_joint_entry
    (result : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (left right : (Context base noQuantum m ell width).quantumLayout.Basis)
    (leftRef rightRef : Reference.Index) :
    ((measuredReset base noQuantum m ell width result).execute environment
        Reference state).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if left (control base noQuantum m ell width) =
          (Context base noQuantum m ell width).quantumLayout.zeroLabel
            (control base noQuantum m ell width) ∧
        right (control base noQuantum m ell width) =
          (Context base noQuantum m ell width).quantumLayout.zeroLabel
            (control base noQuantum m ell width) then
        ∑ entry : Store (Context base noQuantum m ell width) × (model.HiddenState × History),
          ∑ outcome : Fin ((Context base noQuantum m ell width).quantumLayout.wire
              (control base noQuantum m ell width)).dimension,
            (state.block entry).matrix
              (Function.update left (control base noQuantum m ell width) outcome, leftRef)
              (Function.update right (control base noQuantum m ell width) outcome, rightRef)
      else 0 := by
  exact ZReset.zReset_execute_entry (allowAllocation := true)
    (gates := AlgorithmGate.model) (oracles := .empty)
    (ctx := Context base noQuantum m ell width)
    (environment := ⟨environment.quantum, environment.classical⟩) (services := .empty)
    (control base noQuantum m ell width) (dimensionedCell base noQuantum m ell width result)
    (realizations base noQuantum m ell width) state left right leftRef rightRef

/-- No complete joint result/history block has a nonzero control row after the actual reset. -/
lemma measuredReset_block_zero
    (result : CWriteRef (Context base noQuantum m ell width) (.finite 2))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (entry : Store (Context base noQuantum m ell width) ×
      (model.HiddenState ×
        (History × (measuredReset base noQuantum m ell width result).Path)))
    (left right : (Context base noQuantum m ell width).quantumLayout.Basis)
    (leftRef rightRef : Reference.Index)
    (nonzero : left (control base noQuantum m ell width) ≠
      (Context base noQuantum m ell width).quantumLayout.zeroLabel
        (control base noQuantum m ell width)) :
    (((measuredReset base noQuantum m ell width result).execute environment Reference state).block
      entry).matrix (left, leftRef) (right, rightRef) = 0 := by
  exact ZReset.zReset_execute_block_selected_zero
    (environment := ⟨environment.quantum, environment.classical⟩) (allowAllocation := true)
      (services := .empty)
    (control base noQuantum m ell width) (dimensionedCell base noQuantum m ell width result)
    (realizations base noQuantum m ell width) state entry left right leftRef rightRef nonzero

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling
