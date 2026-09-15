/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Observation
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Selecting the existing persistent acceptance bit

Local execution preserves the stored acceptance bit separately from the
selected word. Every joint observation on one acceptance fiber is therefore
the observation of the actual interpreter on that input fiber. The selected
word, all other classical cells, history and external reference remain arbitrary.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Local execution preserves a common acceptance bit without fixing the selected word. -/
theorem underPersistent_acceptance_supported
    (code : Circuit ctx ctx) (supported : code.IsLocal) (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H) (flag : Bool)
    (holds : ∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
        flag)
    (result : Store (persistentCtx ctx width scalarWidth) ×
      (H × (underPersistent code supported width scalarWidth).Path))
    (positive : 0 < (((underPersistent code supported width scalarWidth).execute
      Reference state).block result).mass) :
    (result.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool =
      flag := by
  have kept := retained_observation_supported (persistentCoordinates ctx width scalarWidth)
    (persistentStores ctx width scalarWidth) (@persistentStores_mass kind ctx width scalarWidth)
    code (underPersistent code supported width scalarWidth)
    (underPersistentPathEquiv code supported width scalarWidth)
    (@persistentCoordinates_execute kind ctx code supported width scalarWidth)
    (fun history => (savedLatches width scalarWidth history).1) flag state
    (fun original positive =>
      (congrArg Prod.fst (persistentStores_latches width scalarWidth original.1)).trans
        (holds original positive)) result positive
  exact (congrArg Prod.fst (persistentStores_latches width scalarWidth result.1)).symm.trans kept

private theorem gated_weight_supported {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (read : C → Bool) (flag wanted : Bool)
    (effects : C → Effect R)
    (holds : ∀ entry, 0 < (state.block entry).mass → read entry = flag) :
    state.effectWeight (fun entry => if read entry = wanted then effects entry else Effect.zero R) =
      if flag = wanted then state.effectWeight effects else 0 := by
  classical
  have termwise : ∀ entry,
      (if read entry = wanted then effects entry else Effect.zero R).weight (state.block entry) =
        if flag = wanted then (effects entry).weight (state.block entry) else 0 := by
    intro entry
    by_cases positive : 0 < (state.block entry).mass
    · rw [holds entry positive]
      split_ifs <;> simp only [Effect.weight_zero]
    · have zeroMass : (state.block entry).mass = 0 :=
        le_antisymm (le_of_not_gt positive) (state.block entry).mass_nonneg
      rw [state.block_eq_zero_of_mass_eq_zero entry zeroMass]
      split_ifs <;> simp [Effect.weight]
  simp only [ExecutionState.effectWeight, termwise]
  split_ifs <;> simp

private theorem execute_weight_select_sum {pre post : RuntimeCtx kind}
    (code : Circuit pre post) {Reference : Register} {H : Type} [Fintype H]
    (state : State pre Reference H) (read : Store pre × H → Bool)
    (effects : Circuit.EffectFamily post Reference (H × code.Path)) :
    (code.execute Reference state).effectWeight effects =
      ∑ flag : Bool, (code.execute Reference (state.selectClassical read flag)).effectWeight
        effects := by
  simp only [Circuit.effectWeight_execute]
  have same := congrArg (fun current : State pre Reference H =>
    current.effectWeight (code.effectPullback Reference effects))
      (ExecutionState.finiteSum_selectClassical state read)
  rw [ExecutionState.effectWeight_finiteSum] at same
  exact same.symm

private theorem selected_supported {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (read : C → Bool) (flag : Bool)
    (entry : C) (positive : 0 < ((state.selectClassical read flag).block entry).mass) :
    read entry = flag := by
  apply ExecutionState.selectClassical_read_eq_of_block_ne_zero state read flag entry
  intro zero
  rw [zero, DensityOperator.zero_mass] at positive
  exact (lt_irrefl 0) positive

private theorem execute_gated_weight {pre post : RuntimeCtx kind}
    (code : Circuit pre post) {Reference : Register} {H : Type} [Fintype H]
    (readInput : Store pre × H → Bool) (readOutput : Store post × (H × code.Path) → Bool)
    (preserves : ∀ (state : State pre Reference H) (flag : Bool),
      (∀ entry, 0 < (state.block entry).mass → readInput entry = flag) →
      ∀ entry, 0 < ((code.execute Reference state).block entry).mass → readOutput entry = flag)
    (state : State pre Reference H) (wanted : Bool)
    (effects : Circuit.EffectFamily post Reference (H × code.Path)) :
    (code.execute Reference state).effectWeight
        (fun entry => if readOutput entry = wanted then effects entry else Effect.zero _) =
      (code.execute Reference (state.selectClassical readInput wanted)).effectWeight effects := by
  rw [execute_weight_select_sum code state readInput]
  have summands : ∀ flag : Bool,
      (code.execute Reference (state.selectClassical readInput flag)).effectWeight
          (fun entry => if readOutput entry = wanted then effects entry else Effect.zero _) =
        if flag = wanted then
          (code.execute Reference (state.selectClassical readInput flag)).effectWeight effects
        else 0 := by
    intro flag
    exact gated_weight_supported _ readOutput flag wanted effects
      (preserves _ flag (selected_supported state readInput flag))
  simp only [summands, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- A joint observation at one acceptance value equals execution on that actual input fiber. -/
theorem underPersistent_acceptance_effectWeight
    (code : Circuit ctx ctx) (supported : code.IsLocal) (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H) (flag : Bool)
    (effects : Circuit.EffectFamily (persistentCtx ctx width scalarWidth) Reference
      (H × (underPersistent code supported width scalarWidth).Path)) :
    ((underPersistent code supported width scalarWidth).execute Reference state).effectWeight
        (fun entry => if (entry.1.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = flag
          then effects entry else Effect.zero _) =
      ((underPersistent code supported width scalarWidth).execute Reference
        (state.selectClassical (fun entry => (entry.1.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool)
            flag)).effectWeight effects := by
  exact execute_gated_weight (underPersistent code supported width scalarWidth) _ _
    (fun current selected holds =>
      underPersistent_acceptance_supported code supported width scalarWidth
        current selected holds) state flag effects

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
