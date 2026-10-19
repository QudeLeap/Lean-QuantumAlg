/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Acceptance.Weight
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Embedding.Observation
import all QuantumAlg.Core.Execution.Circuit.Effect

/-!
# Actual failure contraction on the original unaccepted input fiber

The real sampler keeps the original acceptance bit. Its joint failure event
therefore equals sampling the original unaccepted blocks, retaining their
actual masses. Complete checked recovery rejects precisely the complement
of its original candidate condition on that fiber. A floor proved for that
same physical execution gives the resulting failure contraction.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve ClassicalAlgorithms.Modular

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma indicator_weight {R : Register} (state : DensityOperator R)
    (condition : Prop) [Decidable condition] :
    (if condition then Effect.one R else Effect.zero R).weight state =
      if condition then state.mass else 0 := by
  split_ifs <;> simp only [Effect.weight_one, Effect.weight_zero]

private lemma complement_weight {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (condition : C → Prop) [DecidablePred condition] :
    state.effectWeight (fun value => if ¬condition value then Effect.one R else Effect.zero R) =
      state.mass - state.effectWeight
        (fun value => if condition value then Effect.one R else Effect.zero R) := by
  simp only [ExecutionState.effectWeight, ExecutionState.mass, indicator_weight]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro value _
  by_cases selected : condition value <;> simp [selected]

private lemma selected_mass {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (read : C → Bool) (flag : Bool) :
    (state.selectClassical read flag).mass =
      state.effectWeight
        (fun value => if read value = flag then Effect.one R else Effect.zero R) := by
  rw [ExecutionState.selectClassical_mass]
  unfold ExecutionState.effectWeight
  apply Finset.sum_congr rfl
  intro value _
  by_cases selected : read value = flag <;>
    simp only [selected, if_true, if_false, Effect.weight_one, Effect.weight_zero]

private lemma storedWeight_seq {model : ExecutionModel} {environment : model.Environment}
    {origin middle final : RuntimeCtx model.kind}
    (first : Circuit model origin middle) (second : Circuit model middle final)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State origin Reference (model.HiddenState × H))
    (effects : Store final → Effect (final.register.prod Reference)) :
    ((first.seq second).execute environment Reference state).effectWeight (fun entry => effects
      entry.1) =
      (second.execute environment Reference (first.execute environment Reference
        state)).effectWeight
        (fun entry => effects entry.1) := by
  rw [Circuit.execute_seq, State.effectWeight_mapHistory]

private lemma execution_complement_le {model : ExecutionModel} {environment : model.Environment}
    {ctx : RuntimeCtx model.kind}
    (code : Circuit model ctx ctx) {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference (model.HiddenState × H))
    (eligible : Store ctx → Prop) [DecidablePred eligible]
    (lower : ℝ)
    (bound : state.mass * lower ≤ (code.execute environment Reference state).effectWeight
      (fun entry => if eligible entry.1 then Effect.one _ else Effect.zero _)) :
    (code.execute environment Reference state).effectWeight
      (fun entry => if ¬eligible entry.1 then Effect.one _ else Effect.zero _) ≤
        (1 - lower) * state.mass := by
  rw [complement_weight, Circuit.execute_mass]
  linarith

private lemma gated_weight_supported {C : Type} [Fintype C] {R : Register}
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

private lemma selected_supported {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (read : C → Bool) (flag : Bool)
    (entry : C) (positive : 0 < ((state.selectClassical read flag).block entry).mass) :
    read entry = flag := by
  apply ExecutionState.selectClassical_read_eq_of_block_ne_zero state read flag entry
  intro zero
  rw [zero, DensityOperator.zero_mass] at positive
  exact (lt_irrefl 0) positive

private lemma execute_gated_weight {model : ExecutionModel} {environment : model.Environment}
    {pre post : RuntimeCtx model.kind}
    (code : Circuit model pre post) {Reference : Register} {H : Type} [Fintype H]
    (readInput : Store pre × (model.HiddenState × H) → Bool)
    (readOutput : Store post × (model.HiddenState × (H × code.Path)) → Bool)
    (preserves : ∀ (state : State pre Reference (model.HiddenState × H)) (flag : Bool),
      (∀ entry, 0 < (state.block entry).mass → readInput entry = flag) →
      ∀ entry, 0 < ((code.execute environment Reference state).block entry).mass → readOutput
        entry = flag)
    (state : State pre Reference (model.HiddenState × H)) (wanted : Bool)
    (effects : Circuit.EffectFamily post Reference
      (model.HiddenState × (H × code.Path))) :
    (code.execute environment Reference state).effectWeight
        (fun entry => if readOutput entry = wanted then effects entry else Effect.zero _) =
      (code.execute environment Reference (state.selectClassical readInput wanted)).effectWeight
        effects := by
  rw [Circuit.effectWeight_execute_partition code environment state readInput]
  have summands : ∀ flag : Bool,
      (code.execute environment Reference (state.selectClassical readInput flag)).effectWeight
          (fun entry => if readOutput entry = wanted then effects entry else Effect.zero _) =
        if flag = wanted then
          (code.execute environment Reference (state.selectClassical readInput
            flag)).effectWeight effects
        else 0 := by
    intro flag
    exact gated_weight_supported _ readOutput flag wanted effects
      (preserves _ flag (selected_supported state readInput flag))
  simp only [summands, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private lemma sampleUnderPersistent_acceptance_effectWeight
    {model : ExecutionModel} {environment : model.Environment} {ctx : RuntimeCtx model.kind}
    (code : Circuit model ctx ctx false) (width scalarWidth : Nat)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (flag : Bool)
    (effects : Circuit.EffectFamily (persistentCtx ctx width scalarWidth) Reference
      (model.HiddenState × (H × (sampleUnderPersistent code width scalarWidth).Path))) :
    ((sampleUnderPersistent code width scalarWidth).execute environment Reference
      state).effectWeight
        (fun entry => if (entry.1.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = flag
          then effects entry else Effect.zero _) =
      ((sampleUnderPersistent code width scalarWidth).execute environment Reference
        (state.selectClassical (fun entry => (entry.1.read
          (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool)
            flag)).effectWeight effects := by
  refine execute_gated_weight (sampleUnderPersistent code width scalarWidth) _ _ ?_
    state flag effects
  intro current selected holds entry positive
  exact candidateCheck_sampleUnderPersistent_latches_property code width scalarWidth
    current (fun pair => pair.1 = selected) holds entry positive

variable {model : ExecutionModel} {environment : model.Environment} {environment :
  model.Environment} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width scalarWidth : Nat}

local instance (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (basePoint targetPoint : Pure.Point curve)
    (sample : CShape.Value (.fixedVector (scalarWidth + scalarWidth) (.finite 2))) :
    Decidable (SampleAccepted curve modulus basePoint targetPoint sample) := by
  unfold SampleAccepted
  infer_instance

/-- Actual subnormalized mass of the existing unaccepted records. -/
def persistentFailureWeight {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H)) : ℝ :=
  state.effectWeight (fun entry => if (entry.1.read
    (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
      Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
    else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))

private lemma sampled_failure_weight
    (actual : Circuit model (persistentCtx ctx width scalarWidth)
      (persistentCtx ctx width scalarWidth))
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (represents : ∀ entry, 0 < ((actual.execute environment Reference state).block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
      ((actual.seq (persistentAttempt curve modulus sample base target)).execute environment
        Reference state) =
      (actual.execute environment Reference state).effectWeight (fun entry => if (entry.1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false ∧
          ¬SampleAccepted curve modulus basePoint targetPoint
            (entry.1.read (persistentInput width scalarWidth sample)) then
          Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
        else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference)) := by
  exact (storedWeight_seq actual (persistentAttempt curve modulus sample base target) state
    (fun store => if (store.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
        Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
      else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))).trans
    (persistentAttempt_failure_weight curve modulus sample base target
      basePoint targetPoint (actual.execute environment Reference state) represents)

private lemma conjunction_effectWeight {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (before current : C → Prop)
    [DecidablePred before] [DecidablePred current] :
    state.effectWeight (fun value => if before value ∧ current value then
      Effect.one R else Effect.zero R) =
    state.effectWeight (fun value => if before value then
      (if current value then Effect.one R else Effect.zero R) else Effect.zero R) := by
  congr 1
  funext value
  by_cases selected : before value <;> simp [selected]

attribute [local irreducible] sampleUnderPersistent

/-- A proved candidate floor on the real failure fiber contracts the actual sampled attempt. -/
lemma sampledAttempt_failure_weight_le
    (sampleCode : Circuit model ctx ctx false)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference (model.HiddenState × H))
    (represents : ∀ entry, 0 < (((sampleUnderPersistent sampleCode width scalarWidth).execute
      environment
      Reference state).block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint)
    (lower : ℝ)
    (bound :
      let rejected := state.selectClassical (fun entry => (entry.1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool) false
      rejected.mass * lower ≤
        ((sampleUnderPersistent sampleCode width scalarWidth).execute environment
          Reference rejected).effectWeight (fun entry =>
            if SampleAccepted curve modulus basePoint targetPoint
            (entry.1.read (persistentInput width scalarWidth sample)) then
              Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
            else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
      ((sampledAttempt sampleCode curve modulus sample base target).execute environment
        Reference state) ≤ (1 - lower) *
          persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
            state := by
  let read := fun entry : Store (persistentCtx ctx width scalarWidth) ×
      (model.HiddenState × H) =>
    (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool
  let rejected := state.selectClassical read false
  let eligible := fun store : Store (persistentCtx ctx width scalarWidth) =>
    SampleAccepted curve modulus basePoint targetPoint
      (store.read (persistentInput width scalarWidth sample))
  have checked := sampled_failure_weight (environment := environment)
    (sampleUnderPersistent sampleCode width scalarWidth) curve modulus sample
    base target basePoint targetPoint state
    (fun entry positive => represents entry positive)
  have grouped := conjunction_effectWeight
    ((sampleUnderPersistent sampleCode width scalarWidth).execute environment Reference state)
    (fun entry => (entry.1.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false)
    (fun entry => ¬eligible entry.1)
  have selected := sampleUnderPersistent_acceptance_effectWeight (environment := environment)
    sampleCode width scalarWidth state false
    (fun entry => if ¬eligible entry.1 then
      Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
    else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))
  have contraction := execution_complement_le
    (sampleUnderPersistent sampleCode width scalarWidth) rejected eligible lower bound
  exact (checked.trans (grouped.trans selected)).trans_le
    (contraction.trans_eq (congrArg ((1 - lower) * ·) (selected_mass state read false)))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
