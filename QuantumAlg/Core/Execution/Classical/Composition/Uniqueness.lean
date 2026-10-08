/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Classical.Composition.Record
import all QuantumAlg.Core.Execution.Probability

/-!
# Uniqueness of complete actual execution records

A definite classical input with positive quantum mass distinguishes different
returned stores or paths. Thus two records certifying the same existing
interpreter on all complete states are the same function. This principle
preserves both state and exact-path evidence when composing separate proofs.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

private theorem mapped_value_mass {C D : Type} [Fintype C] [Fintype D] {R : Register}
    [DecidableEq C] [DecidableEq D]
    (source : C) (density : DensityOperator R) (update : C → D) (target : D) :
    (((ofValue source density).mapClassical update).block target).mass =
      if update source = target then density.mass else 0 := by
  rw [mapClassical_block_mass]
  simp only [ofValue_block, apply_ite DensityOperator.mass, DensityOperator.zero_mass]
  rw [Finset.sum_eq_single source]
  · simp
  · intro other _ different
    simp only [if_neg different, ite_self]
  · simp

end ExecutionState

private theorem maps_unique {C D : Type} [Fintype C] [Fintype D] {R : Register}
    [DecidableEq D]
    (density : DensityOperator R) (normalized : density.mass = 1) (first second : C → D)
    (equation : ∀ state : ExecutionState C R,
      state.mapClassical first = state.mapClassical second) : first = second := by
  funext source
  have observed := congrArg (fun final => (final.block (first source)).mass)
    (equation (ExecutionState.ofValue source density))
  rw [ExecutionState.mapped_value_mass, ExecutionState.mapped_value_mass] at observed
  simp only [if_true] at observed
  rw [normalized] at observed
  by_cases same : second source = first source
  · exact same.symm
  · simp only [if_neg same] at observed
    norm_num at observed

namespace Circuit

open Execution

/-- Complete equations for the same actual interpreter determine both store and path uniquely. -/
theorem executionRecord_unique {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (code : Circuit model ctx ctx)
    (first second : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × code.Path)
    (firstEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      code.execute Reference state = state.mapClassical (fun entry =>
        let result := first (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2)))))
    (secondEquation : ∀ (Reference : Register) {History : Type} [Fintype History]
      (state : State ctx Reference (model.HiddenState × History)),
      code.execute Reference state = state.mapClassical (fun entry =>
        let result := second (entry.1, entry.2.1)
        (result.1.1, (result.1.2, (entry.2.2, result.2))))) : first = second := by
  let density : DensityOperator (Register.prod ctx.register (Qubits 0)) :=
    DensityOperator.ofPure (NormalizedVector.ket (ctx.quantumLayout.zeroLabel, 0))
  let firstMap : Store ctx × (model.HiddenState × Unit) →
      Store ctx × (model.HiddenState × (Unit × code.Path)) := fun entry =>
    let result := first (entry.1, entry.2.1)
    (result.1.1, (result.1.2, (entry.2.2, result.2)))
  let secondMap : Store ctx × (model.HiddenState × Unit) →
      Store ctx × (model.HiddenState × (Unit × code.Path)) := fun entry =>
    let result := second (entry.1, entry.2.1)
    (result.1.1, (result.1.2, (entry.2.2, result.2)))
  have equation : ∀ state : State ctx (Qubits 0) (model.HiddenState × Unit),
      state.mapClassical firstMap = state.mapClassical secondMap := by
    intro state
    convert (firstEquation (Qubits 0) state).symm.trans
      (secondEquation (Qubits 0) state) using 1 <;>
      congr 1 <;> exact Subsingleton.elim _ _
  have same := maps_unique density (DensityOperator.ofPure_normalized _) firstMap secondMap equation
  funext input
  exact congrArg (fun entry => ((entry.1, entry.2.1), entry.2.2.2))
    (congrFun same (input.1, (input.2, ())))

end Circuit

end

end QuantumAlg
