/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling

import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.Acceptance.Weight
import all
  QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent.Local.Selection

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

private theorem indicator_weight {R : Register} (state : DensityOperator R)
    (condition : Prop) [Decidable condition] :
    (if condition then Effect.one R else Effect.zero R).weight state =
      if condition then state.mass else 0 := by
  split_ifs <;> simp only [Effect.weight_one, Effect.weight_zero]

private theorem complement_weight {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (condition : C → Prop) [DecidablePred condition] :
    state.effectWeight (fun value => if ¬condition value then Effect.one R else Effect.zero R) =
      state.mass - state.effectWeight
        (fun value => if condition value then Effect.one R else Effect.zero R) := by
  simp only [ExecutionState.effectWeight, ExecutionState.mass, indicator_weight]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro value _
  by_cases selected : condition value <;> simp [selected]

private theorem selected_mass {C : Type} [Fintype C] {R : Register}
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

private theorem storedWeight_seq {kind : ProblemKind}
    {origin middle final : RuntimeCtx kind}
    (first : Circuit origin middle) (second : Circuit middle final)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State origin Reference H)
    (effects : Store final → Effect (final.register.prod Reference)) :
    ((first.seq second).execute Reference state).effectWeight (fun entry => effects entry.1) =
      (second.execute Reference (first.execute Reference state)).effectWeight
        (fun entry => effects entry.1) := by
  rw [Circuit.execute_seq, State.effectWeight_mapHistory]

private theorem execution_complement_le {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (code : Circuit ctx ctx) {Reference : Register} {H : Type} [Fintype H]
    (state : State ctx Reference H) (eligible : Store ctx → Prop) [DecidablePred eligible]
    (lower : ℝ)
    (bound : state.mass * lower ≤ (code.execute Reference state).effectWeight
      (fun entry => if eligible entry.1 then Effect.one _ else Effect.zero _)) :
    (code.execute Reference state).effectWeight
      (fun entry => if ¬eligible entry.1 then Effect.one _ else Effect.zero _) ≤
        (1 - lower) * state.mass := by
  rw [complement_weight, Circuit.execute_mass]
  linarith

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width scalarWidth : Nat}

local instance (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (basePoint targetPoint : Pure.Point curve)
    (sample : CShape.Value (.fixedVector (scalarWidth + scalarWidth) (.finite 2))) :
    Decidable (SampleAccepted curve modulus basePoint targetPoint sample) := by
  unfold SampleAccepted
  infer_instance

/-- Actual subnormalized mass of the existing unaccepted records. -/
def persistentFailureWeight {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H) : ℝ :=
  state.effectWeight (fun entry => if (entry.1.read
    (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false then
      Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
    else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))

private theorem sampled_failure_weight
    (actual : Circuit (persistentCtx ctx width scalarWidth)
      (persistentCtx ctx width scalarWidth))
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H)
    (represents : ∀ entry, 0 < ((actual.execute Reference state).block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
      ((actual.seq (persistentAttempt curve modulus sample base target)).execute Reference state) =
      (actual.execute Reference state).effectWeight (fun entry => if (entry.1.read
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
    (@persistentAttempt_failure_weight kind ctx width scalarWidth curve modulus sample base target
      basePoint targetPoint Reference (H × actual.Path) inferInstance
      (actual.execute Reference state) represents)

private theorem conjunction_effectWeight {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (before current : C → Prop)
    [DecidablePred before] [DecidablePred current] :
    state.effectWeight (fun value => if before value ∧ current value then
      Effect.one R else Effect.zero R) =
    state.effectWeight (fun value => if before value then
      (if current value then Effect.one R else Effect.zero R) else Effect.zero R) := by
  congr 1
  funext value
  by_cases selected : before value <;> simp [selected]

attribute [local irreducible] underPersistent

/-- A proved candidate floor on the real failure fiber contracts the actual sampled attempt. -/
theorem sampledAttempt_failure_weight_le
    (sampleCode : Circuit ctx ctx) (supported : sampleCode.IsLocal)
    (curve : CurveSpec width) (modulus : ModulusSpec scalarWidth)
    (sample : CInputRef ctx (.fixedVector (scalarWidth + scalarWidth) (.finite 2)))
    (base target : CInputRef ctx (PointShape width)) (basePoint targetPoint : Pure.Point curve)
    {Reference : Register} {H : Type} [Fintype H]
    (state : State (persistentCtx ctx width scalarWidth) Reference H)
    (represents : ∀ entry, 0 < (((underPersistent sampleCode supported width scalarWidth).execute
      Reference state).block entry).mass →
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth base)) basePoint ∧
      PointRepresents curve (entry.1.read (persistentInput width scalarWidth target)) targetPoint)
    (lower : ℝ)
    (bound :
      let rejected := state.selectClassical (fun entry => (entry.1.read
        (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool) false
      rejected.mass * lower ≤
        ((underPersistent sampleCode supported width scalarWidth).execute
          Reference rejected).effectWeight (fun entry =>
            if SampleAccepted curve modulus basePoint targetPoint
            (entry.1.read (persistentInput width scalarWidth sample)) then
              Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
            else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))) :
    persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
      ((sampledAttempt sampleCode supported curve modulus sample base target).execute
        Reference state) ≤ (1 - lower) *
          persistentFailureWeight (ctx := ctx) (width := width) (scalarWidth := scalarWidth)
            state := by
  let read := fun entry : Store (persistentCtx ctx width scalarWidth) × H =>
    (entry.1.read (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool
  let rejected := state.selectClassical read false
  let eligible := fun store : Store (persistentCtx ctx width scalarWidth) =>
    SampleAccepted curve modulus basePoint targetPoint
      (store.read (persistentInput width scalarWidth sample))
  have checked := @sampled_failure_weight kind ctx width scalarWidth
    (underPersistent sampleCode supported width scalarWidth) curve modulus sample
    base target basePoint targetPoint Reference H inferInstance state
    (fun entry positive => represents entry positive)
  have grouped := conjunction_effectWeight
    ((underPersistent sampleCode supported width scalarWidth).execute Reference state)
    (fun entry => (entry.1.read
      (.storage (persistentAccepted ctx width scalarWidth).toCStorageRef)).toBool = false)
    (fun entry => ¬eligible entry.1)
  have selected := @underPersistent_acceptance_effectWeight kind ctx sampleCode supported width
    scalarWidth Reference H inferInstance state false
    (fun entry => if ¬eligible entry.1 then
      Effect.one ((persistentCtx ctx width scalarWidth).register.prod Reference)
    else Effect.zero ((persistentCtx ctx width scalarWidth).register.prod Reference))
  have contraction := execution_complement_le
    (underPersistent sampleCode supported width scalarWidth) rejected eligible lower bound
  exact (checked.trans (grouped.trans selected)).trans_le
    (contraction.trans_eq (congrArg ((1 - lower) * ·) (selected_mass state read false)))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
