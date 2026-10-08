/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.QuditShift.Reset
import all QuantumAlg.Core.Execution.Quantum.Step

/-!
# Stored Z results select their cyclic correction

This mathematical composition uses the existing Z-write and conditional
state updates. The measured value is written into a typed finite
classical register, then read from that register to choose its negative shift.
The result retains the complete classical store and full quantum state.

The state calculation instantiates the local projective update
[dW19, qcnotes.tex:5420] and the following unitary action
[dW19, qcnotes.tex:5405]. The formulas below sum all old stores that produce the
same new store, so overwriting a classical value does not assume injectivity.
-/

section

namespace QuantumAlg.QuditShift

open Execution

noncomputable section

variable {systemCount : Nat} {layout : QuantumLayout systemCount}
  {ctx : RuntimeCtx .quantum}

local instance : DecidableEq (Store ctx) := Classical.decEq _

private instance feedForwardDimensionNeZero (dimension : ℕ+) : NeZero (dimension : ℕ) :=
  ⟨Nat.ne_of_gt dimension.property⟩

/-- Measure into the actual writable register, then read it to select the shift. -/
def resetAfterZWrite (state : ExecutionState (Store ctx) layout.register)
    (wire : Fin systemCount)
    (output : CWriteRef ctx (.finite (layout.wire wire).dimension)) :
    ExecutionState (Store ctx) layout.register :=
  conditional (writeZ state wire output) (.storage output.toCStorageRef)
    (fun outcome => operator layout wire (-outcome))

/-- The gate selected by the stored result is exactly the negative-outcome
operator applied to that measurement branch. -/
theorem resetAfterZWrite_eq (state : ExecutionState (Store ctx) layout.register)
    (wire : Fin systemCount)
    (output : CWriteRef ctx (.finite (layout.wire wire).dimension)) :
    resetAfterZWrite state wire output =
      ((state.measureZ fun basis : layout.Basis => basis wire).applyUnitary fun result =>
        (operator layout wire (-result.2))).mapClassical fun result =>
          result.1.write output (.finite result.2) :=
  conditional_writeZ state wire output (fun outcome => operator layout wire (-outcome))

/-- Exact final-store matrix entries, summing all old stores and outcomes that
actually write that final store. Every other quantum system remains in the block. -/
theorem resetAfterZWrite_block_entry (state : ExecutionState (Store ctx) layout.register)
    (wire : Fin systemCount)
    (output : CWriteRef ctx (.finite (layout.wire wire).dimension))
    (finalStore : Store ctx) (left right : layout.Basis) :
    ((resetAfterZWrite state wire output).block finalStore).matrix left right =
      ∑ oldStore, ∑ outcome,
        if oldStore.write output (.finite outcome) = finalStore then
          if left wire = 0 ∧ right wire = 0 then
            (state.block oldStore).matrix (Function.update left wire outcome)
              (Function.update right wire outcome)
          else 0
        else 0 := by
  rw [resetAfterZWrite_eq]
  change (∑ result : Store ctx × Fin (layout.wire wire).dimension,
    if result.1.write output (.finite result.2) = finalStore then
      (resetBranch layout wire result.2 (state.block result.1)).matrix
    else 0) left right = _
  calc
    _ = ∑ result : Store ctx × Fin (layout.wire wire).dimension,
        (if result.1.write output (.finite result.2) = finalStore then
          (resetBranch layout wire result.2 (state.block result.1)).matrix
        else (0 : Matrix layout.Basis layout.Basis ℂ)) left right :=
      Matrix.sum_apply left right Finset.univ _
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro oldStore _
      apply Finset.sum_congr rfl
      intro outcome _
      by_cases written : oldStore.write output (.finite outcome) = finalStore
      · simp only [written, if_true]
        exact resetBranch_entry layout wire outcome (state.block oldStore) left right
      · simp only [written, if_false]
        rfl

/-- Summing the classical blocks leaves zero on the selected wire and retains
the original joint marginal of the other systems, including all coherences. -/
theorem resetAfterZWrite_quantum_entry (state : ExecutionState (Store ctx) layout.register)
    (wire : Fin systemCount)
    (output : CWriteRef ctx (.finite (layout.wire wire).dimension))
    (left right : layout.Basis) :
    (resetAfterZWrite state wire output).quantumMarginal.matrix left right =
      if left wire = 0 ∧ right wire = 0 then
        ∑ oldStore, ∑ outcome,
          (state.block oldStore).matrix (Function.update left wire outcome)
            (Function.update right wire outcome)
      else 0 := by
  rw [resetAfterZWrite_eq, ExecutionState.mapClassical_quantumMarginal]
  change (∑ result : Store ctx × Fin (layout.wire wire).dimension,
    (resetBranch layout wire result.2 (state.block result.1)).matrix) left right = _
  calc
    _ = ∑ result : Store ctx × Fin (layout.wire wire).dimension,
        (resetBranch layout wire result.2 (state.block result.1)).matrix left right :=
      Matrix.sum_apply left right Finset.univ _
    _ = _ := by
      simp only [Fintype.sum_prod_type, resetBranch_entry]
      by_cases h : left wire = 0 ∧ right wire = 0 <;> simp [h]

/-- The concrete write/read sequence preserves the complete execution mass. -/
theorem resetAfterZWrite_mass (state : ExecutionState (Store ctx) layout.register)
    (wire : Fin systemCount)
    (output : CWriteRef ctx (.finite (layout.wire wire).dimension)) :
    (resetAfterZWrite state wire output).mass = state.mass := by
  rw [resetAfterZWrite, conditional_mass, writeZ_mass]

private def qutritQubitLayout : QuantumLayout 2 :=
  QuantumLayout.ofWires [⟨0, 3⟩, ⟨1, 2⟩] (by decide)

/-- A qutrit Z result is written to a three-valued classical register before
the selected gate resets it, while the second physical system is a qubit. -/
theorem qutritZWrite_reset_zero
    (state : ExecutionState (Store ctx) qutritQubitLayout.register)
    (output : CWriteRef ctx (.finite 3)) (left right : qutritQubitLayout.Basis)
    (nonzero : left 0 ≠ 0) :
    (resetAfterZWrite state 0 output).quantumMarginal.matrix left right = 0 := by
  simpa only [nonzero, false_and, if_false] using
    resetAfterZWrite_quantum_entry state (0 : Fin 2) output left right

/-- The same concrete qutrit write/read sequence retains every matrix entry
of the reference qubit's reduced state, even for an entangled input. -/
theorem qutritZWrite_reference_entry
    (state : ExecutionState (Store ctx) qutritQubitLayout.register)
    (output : CWriteRef ctx (.finite 3)) (left right : qutritQubitLayout.Basis)
    (leftZero : left 0 = 0) (rightZero : right 0 = 0) :
    (resetAfterZWrite state 0 output).quantumMarginal.matrix left right =
      ∑ oldStore, ∑ outcome : Fin 3,
        (state.block oldStore).matrix (Function.update left 0 outcome)
          (Function.update right 0 outcome) := by
  change (resetAfterZWrite state (0 : Fin 2) output).quantumMarginal.matrix left right =
    ∑ oldStore : Store ctx,
      ∑ outcome : Fin (qutritQubitLayout.wire (0 : Fin 2)).dimension,
        (state.block oldStore).matrix (Function.update left (0 : Fin 2) outcome)
          (Function.update right (0 : Fin 2) outcome)
  exact (resetAfterZWrite_quantum_entry (layout := qutritQubitLayout)
    state (0 : Fin 2) output left right).trans (if_pos ⟨leftZero, rightZero⟩)

end

end QuantumAlg.QuditShift

end
