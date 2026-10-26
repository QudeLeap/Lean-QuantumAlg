/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery.Acceptance
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Recovery
import all QuantumAlg.Core.Execution.Classical.Composition.Range.Effect

/-!
# Conditional failure algebra for the actual fresh-feedback attempts

The real restart and allocating thirty-four-window sampler precede the same
explicit-seven nearest checker. Every observation below retains the actual
Store, HiddenState, incoming History, Path and arbitrary Reference.

The sampling floor and public-input protection are internal proof obligations,
not additional public input fields. This module supplies no Born floor and no
unconditional three-attempt success theorem.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Storage

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve
open ClassicalRoutines.EllipticCurve CandidateCheck.Native

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private def candidateWeight {ctx : RuntimeCtx .quantum} {Reference : Register}
    {Label : Type} [Fintype Label] (state : State ctx Reference Label)
    (prior current : Store ctx → Bool) : ℝ :=
  state.effectWeight (fun entry =>
    if prior entry.1 = false ∧ current entry.1 = true then
      Effect.one (ctx.register.prod Reference) else Effect.zero (ctx.register.prod Reference))

private lemma flag_or_false_weight {ctx : RuntimeCtx .quantum} {Reference : Register}
    {Label : Type} [Fintype Label] (state : State ctx Reference Label)
    (prior current : Store ctx → Bool) :
    CheckerTail.readWeight state (fun store => prior store || current store) false =
      CheckerTail.readWeight state prior false - candidateWeight state prior current := by
  unfold CheckerTail.readWeight candidateWeight ExecutionState.effectWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro entry _
  cases priorEq : prior entry.1 <;> cases currentEq : current entry.1 <;>
    simp [flagEffect, priorEq, currentEq]

attribute [local irreducible] candidateWeight

private lemma failure_bound_of_difference (before after good lower : ℝ)
    (difference : after = before - good) (floor : lower * before ≤ good) :
    after ≤ (1 - lower) * before := by
  linarith

private lemma stored_weight_seq {model : ExecutionModel}
    {first middle last : RuntimeCtx model.kind}
    (head : Circuit model first middle) (tail : Circuit model middle last)
    (environment : model.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State first Reference (model.HiddenState × History))
    (effects : Store last → Effect (last.register.prod Reference)) :
    ((head.seq tail).execute environment Reference state).effectWeight
        (fun entry => effects entry.1) =
      (tail.execute environment Reference (head.execute environment Reference state)).effectWeight
        (fun entry => effects entry.1) := by
  rw [Circuit.execute_seq, State.effectWeight_mapHistory]

private lemma stored_weight_code_eq {model : ExecutionModel} {ctx : RuntimeCtx model.kind}
    (first second : Circuit model ctx ctx) (same : first = second)
    (environment : model.Environment) {Reference : Register} {History : Type}
    [Fintype History] (state : State ctx Reference (model.HiddenState × History))
    (effects : Store ctx → Effect (ctx.register.prod Reference)) :
    (first.execute environment Reference state).effectWeight (fun entry => effects entry.1) =
      (second.execute environment Reference state).effectWeight (fun entry => effects entry.1) := by
  cases same
  rfl

private def ScalarContraction (before prepared after good lower : ℝ) : Prop :=
  prepared = before → lower * before ≤ good → after ≤ (1 - lower) * before

private lemma scalar_contraction (before prepared after good lower : ℝ)
    (difference : after = prepared - good) :
    ScalarContraction before prepared after good lower := by
  intro preserved floor
  exact failure_bound_of_difference before after good lower
    (difference.trans (congrArg (fun value : ℝ => value - good) preserved)) floor

attribute [local irreducible] ScalarContraction

private lemma geometric_step (ratio before middle after : ℝ) (count : Nat)
    (nonnegative : 0 ≤ ratio) (tail : after ≤ ratio ^ count * middle)
    (first : middle ≤ ratio * before) : after ≤ ratio ^ (count + 1) * before := by
  have scaled := mul_le_mul_of_nonneg_left first (pow_nonneg nonnegative count)
  exact tail.trans (scaled.trans_eq (by rw [← mul_assoc, ← pow_succ]))

section ReadLoop

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

private lemma read_weight_seq
    (head tail : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (read : Store ctx → Bool) (flag : Bool) :
    CheckerTail.readWeight ((head.seq tail).execute environment Reference state) read flag =
      CheckerTail.readWeight
        (tail.execute environment Reference (head.execute environment Reference state))
        read flag := by
  unfold CheckerTail.readWeight
  exact stored_weight_seq head tail environment state
    (fun store => flagEffect (ctx.register.prod Reference) (read store) flag)

private lemma read_weight_id
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (read : Store ctx → Bool) (flag : Bool) :
    CheckerTail.readWeight ((Circuit.id
      (model := .quantum AlgorithmGate.model .empty BitWord.model services)
      (allowAllocation := true) ctx).execute environment Reference state) read flag =
      CheckerTail.readWeight state read flag := by
  unfold CheckerTail.readWeight
  rw [Circuit.execute_id_mapClassical, ExecutionState.effectWeight_mapClassical_decision]
  rfl

private lemma read_weight_range_successor (count : Nat)
    (body : Fin (count + 1) → Circuit
      (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (read : Store ctx → Bool) (flag : Bool) :
    CheckerTail.readWeight
        ((Circuit.forRange (count + 1) body).execute environment Reference state) read flag =
      CheckerTail.readWeight ((Circuit.forRange count fun index => body index.succ).execute
        environment Reference ((body 0).execute environment Reference state)) read flag := by
  rw [Circuit.forRange]
  exact read_weight_seq (body 0) (Circuit.forRange count fun index => body index.succ)
    environment state read flag

attribute [local irreducible] CheckerTail.readWeight Circuit.execute Circuit.forRange

private lemma range_successor_le_of_invariant {Reference : Register}
    (admitted : {History : Type} → [Fintype History] →
      State ctx Reference (services.HiddenState × History) → Prop)
    (count : Nat) (body : Fin (count + 1) → Circuit
      (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (read : Store ctx → Bool) (flag : Bool)
    (ratio : ℝ) (nonnegative : 0 ≤ ratio)
    (preserves : ∀ index {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)), admitted state →
      admitted ((body index).execute environment Reference state))
    (step : ∀ index {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)), admitted state →
      CheckerTail.readWeight ((body index).execute environment Reference state) read flag ≤
        ratio * CheckerTail.readWeight state read flag)
    (tailBound : ∀ {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)), admitted state →
      CheckerTail.readWeight ((Circuit.forRange count fun index => body index.succ).execute
        environment Reference state) read flag ≤
        ratio ^ count * CheckerTail.readWeight state read flag)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (initial : admitted state) :
    CheckerTail.readWeight
        ((Circuit.forRange (count + 1) body).execute environment Reference state) read flag ≤
      ratio ^ (count + 1) * CheckerTail.readWeight state read flag := by
  have expression := read_weight_range_successor count body environment state read flag
  have second := tailBound ((body 0).execute environment Reference state)
    (preserves 0 state initial)
  have first := step 0 state initial
  exact expression.le.trans (geometric_step ratio _ _ _ count nonnegative second first)

private lemma range_weight_le_of_invariant {Reference : Register}
    (admitted : {History : Type} → [Fintype History] →
      State ctx Reference (services.HiddenState × History) → Prop)
    (count : Nat) (body : Fin count → Circuit
      (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (read : Store ctx → Bool) (flag : Bool)
    (ratio : ℝ) (nonnegative : 0 ≤ ratio)
    (preserves : ∀ index {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)), admitted state →
      admitted ((body index).execute environment Reference state))
    (step : ∀ index {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)), admitted state →
      CheckerTail.readWeight ((body index).execute environment Reference state) read flag ≤
        ratio * CheckerTail.readWeight state read flag)
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (initial : admitted state) :
    CheckerTail.readWeight
        ((Circuit.forRange count body).execute environment Reference state) read flag ≤
      ratio ^ count * CheckerTail.readWeight state read flag := by
  induction count generalizing History with
  | zero => rw [Circuit.forRange, read_weight_id, pow_zero, one_mul]
  | succ count ih =>
      exact range_successor_le_of_invariant (services := services) (ctx := ctx) admitted count body
        environment read flag ratio nonnegative preserves step
        (fun current holds => ih (fun index => body index.succ)
          (fun index => preserves index.succ) (fun index => step index.succ) current holds)
        state initial

end ReadLoop

namespace FailureAlgebra

variable {ctx : RuntimeCtx .quantum} {width scalarWidth : Nat}
    {services : ClassicalOracleModel}
    (preparedCode actualCode : Circuit
      (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx)
    (tail : CheckerTail ctx width scalarWidth)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

private def Identity : Prop :=
  ∀ (basePoint targetPoint : Pure.Point tail.curve), tail.keys.Nodup →
    (∀ key ∈ tail.keys, key ∉ tail.base.storageKeys) →
    (∀ key ∈ tail.keys, key ∉ tail.target.storageKeys) →
    ∀ {Reference : Register} {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
    (∀ entry, 0 < ((preparedCode.execute environment Reference state).block entry).mass →
      PointRepresents tail.curve (entry.1.read tail.base) basePoint ∧
      PointRepresents tail.curve (entry.1.read tail.target) targetPoint) →
    CheckerTail.readWeight (actualCode.execute environment Reference state) tail.flagRead false =
      CheckerTail.readWeight (preparedCode.execute environment Reference state)
          tail.flagRead false -
        candidateWeight (preparedCode.execute environment Reference state)
          tail.flagRead (tail.eligibleBit basePoint targetPoint)

private lemma identity
    (same : actualCode = preparedCode.seq (tail.code (services := services))) :
    Identity preparedCode actualCode tail environment := by
  unfold Identity
  intro basePoint targetPoint distinct baseFree targetFree Reference History _ state represents
  let prepared := preparedCode.execute environment Reference state
  have checked := tail.flag_weight environment basePoint targetPoint
    distinct baseFree targetFree prepared represents false
  have sequential := stored_weight_seq preparedCode (tail.code (services := services))
    environment state
    (fun store => flagEffect (ctx.register.prod Reference) (tail.flagRead store) false)
  have transported := stored_weight_code_eq actualCode
    (preparedCode.seq (tail.code (services := services))) same environment state
    (fun store => flagEffect (ctx.register.prod Reference) (tail.flagRead store) false)
  exact (transported.trans sequential).trans (checked.trans
    (flag_or_false_weight prepared tail.flagRead
      (tail.eligibleBit basePoint targetPoint)))

private def Bound (lower : ℝ) : Prop :=
  ∀ (basePoint targetPoint : Pure.Point tail.curve), tail.keys.Nodup →
    (∀ key ∈ tail.keys, key ∉ tail.base.storageKeys) →
    (∀ key ∈ tail.keys, key ∉ tail.target.storageKeys) →
    ∀ {Reference : Register} {History : Type} [Fintype History]
      (state : State ctx Reference (services.HiddenState × History)),
    (∀ entry, 0 < ((preparedCode.execute environment Reference state).block entry).mass →
      PointRepresents tail.curve (entry.1.read tail.base) basePoint ∧
      PointRepresents tail.curve (entry.1.read tail.target) targetPoint) →
    ScalarContraction (CheckerTail.readWeight state tail.flagRead false)
      (CheckerTail.readWeight (preparedCode.execute environment Reference state)
        tail.flagRead false)
      (CheckerTail.readWeight (actualCode.execute environment Reference state) tail.flagRead false)
      (candidateWeight (preparedCode.execute environment Reference state)
        tail.flagRead (tail.eligibleBit basePoint targetPoint)) lower

private lemma bound
    (same : actualCode = preparedCode.seq (tail.code (services := services))) (lower : ℝ) :
    Bound preparedCode actualCode tail environment lower := by
  unfold Bound
  intro basePoint targetPoint distinct baseFree targetFree Reference History _ state represents
  have exactDifference := identity preparedCode actualCode tail environment same
    basePoint targetPoint distinct baseFree targetFree state represents
  exact scalar_contraction _ _ _ _ lower exactDifference

private def LoopBound
    (program : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx)
    (read : Store ctx → Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register)
    (admitted : {History : Type} → [Fintype History] →
      State ctx Reference (services.HiddenState × History) → Prop)
    (count : Nat) (lower : ℝ) : Prop :=
  (∀ {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)), admitted state →
    admitted (program.execute environment Reference state)) →
  (∀ {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)), admitted state →
    CheckerTail.readWeight (program.execute environment Reference state) read false ≤
      (1 - lower) * CheckerTail.readWeight state read false) →
  ∀ {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)), admitted state →
    CheckerTail.readWeight
        ((Circuit.forRange count fun _ => program).execute environment Reference state)
        read false ≤ (1 - lower) ^ count * CheckerTail.readWeight state read false

private lemma loop
    (program : Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx)
    (read : Store ctx → Bool)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register)
    (admitted : {History : Type} → [Fintype History] →
      State ctx Reference (services.HiddenState × History) → Prop)
    (count : Nat) (lower : ℝ) (atMostOne : lower ≤ 1) :
    LoopBound program read environment Reference admitted count lower := by
  intro preserves step History _ state initial
  exact range_weight_le_of_invariant admitted count (fun _ => program) environment read false
    (1 - lower) (sub_nonneg.mpr atMostOne) (fun _ => preserves) (fun _ => step) state initial

attribute [local irreducible] Identity Bound LoopBound

end FailureAlgebra

namespace Inputs

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (original : Inputs ctx) (sampler : Sampling.Parameters ctx) (checkers : Checkers ctx)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)

private def preparation : Circuit
    (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx :=
  (original.restart (sampler.output 0)).seq (Sampling.circuit sampler)

private lemma attempt_code_eq : original.attempt sampler checkers =
    (original.preparation sampler).seq
      ((original.checkerTail sampler checkers).code (services := services)) := rfl

attribute [local irreducible] preparation attempt checkerTail CheckerTail.code

/-- Exact failure decomposition for the same restart, allocating sampler and seven checkers. -/
lemma attempt_failure_identity : FailureAlgebra.Identity
    (original.preparation sampler) (original.attempt sampler checkers)
    (original.checkerTail sampler checkers) environment :=
  FailureAlgebra.identity _ _ _ environment (original.attempt_code_eq sampler checkers)

/-- Internal protection and the same actual candidate mass imply one real attempt's contraction. -/
lemma attempt_failure_le (lower : ℝ) : FailureAlgebra.Bound
    (original.preparation sampler) (original.attempt sampler checkers)
    (original.checkerTail sampler checkers) environment lower :=
  FailureAlgebra.bound _ _ _ environment (original.attempt_code_eq sampler checkers) lower

/-- The literal inner loop contracts on its actual invariant states, retaining every path. -/
lemma attempts_failure_le_of_internal_evidence (Reference : Register)
    (admitted : {History : Type} → [Fintype History] →
      State ctx Reference (services.HiddenState × History) → Prop)
    (count : Nat) (lower : ℝ) (atMostOne : lower ≤ 1) :
    FailureAlgebra.LoopBound (original.attempt sampler checkers)
      (original.checkerTail sampler checkers).flagRead environment Reference admitted count lower :=
  FailureAlgebra.loop _ _ environment Reference admitted count lower atMostOne

end Inputs

end

end Storage

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
