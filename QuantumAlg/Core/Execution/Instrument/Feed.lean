/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Instrument.Basic

/-!
# Complete retained blocks around a mathematical unitary feed

The feed is a unitary on the observation space between two actual circuit
interpreters. It introduces no physical instruction or path. Both actual
records, the exact intermediate Store, service state, and incoming history
remain in the same density fibers.
-/

namespace QuantumAlg.Execution

noncomputable section

open Instrument
open scoped BigOperators

attribute [local instance] Classical.decEq

attribute [local instance] Classical.propDecidable

private lemma sandwich_retained_sum {Original Outcome Result : Type}
    [Fintype Original] [Fintype Outcome] [DecidableEq Result] {R : Register}
    (record : Original → Outcome → Result) (parts : Original → Outcome → HilbertOperator R)
    (operator : HilbertOperator R) (result : Result) :
    operator * (∑ original, ∑ outcome,
        if record original outcome = result then parts original outcome else 0) *
          operator.conjTranspose =
      ∑ original, ∑ outcome, if record original outcome = result then
        operator * parts original outcome * operator.conjTranspose else 0 := by
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases selected : record original outcome = result
  · rw [if_pos selected, if_pos selected]
  · simp only [if_neg selected, Matrix.mul_zero, Matrix.zero_mul]

private lemma unitary_retained_blocks {Original Outcome Result : Type}
    [Fintype Original] [Fintype Outcome] [Fintype Result] [DecidableEq Result] {R : Register}
    (state : ExecutionState Original R) (current : ExecutionState Result R)
    (record : Original → Outcome → Result) (operators : Original → Outcome → HilbertOperator R)
    (actual : ∀ result, (current.block result).matrix =
      ∑ original, ∑ outcome, if record original outcome = result then
        operators original outcome * (state.block original).matrix *
          (operators original outcome).conjTranspose else 0)
    (operator : UnitaryOperator R) (result : Result) :
    (((current.applyUnitary (fun _ => operator)).block result).matrix) =
      ∑ original, ∑ outcome, if record original outcome = result then
        (operator : HilbertOperator R) *
          (operators original outcome * (state.block original).matrix *
            (operators original outcome).conjTranspose) *
              (operator : HilbertOperator R).conjTranspose else 0 := by
  rw [ExecutionState.applyUnitary_block, DensityOperator.applyUnitary_matrix, actual]
  exact sandwich_retained_sum _ _ _ _

private def feedKrausOperator {R : Register}
    (last first : HilbertOperator R) (feed : UnitaryOperator R) : HilbertOperator R :=
  last * ((feed : HilbertOperator R) * first)

private def feedSandwich {R : Register} (feed : UnitaryOperator R)
    (first density : HilbertOperator R) : HilbertOperator R :=
  (feed : HilbertOperator R) * (first * density * first.conjTranspose) *
    (feed : HilbertOperator R).conjTranspose

private lemma feedKraus_sandwich {R : Register}
    (last first density : HilbertOperator R) (feed : UnitaryOperator R) :
    last * feedSandwich feed first density * last.conjTranspose =
      feedKrausOperator last first feed * density *
        (feedKrausOperator last first feed).conjTranspose := by
  simp only [feedSandwich, feedKrausOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc]

private lemma feed_composed_sum
    {Original FirstOutcome Intermediate LastOutcome Result : Type}
    [Fintype Original] [Fintype FirstOutcome] [Fintype Intermediate] [Fintype LastOutcome]
    [DecidableEq Intermediate] [DecidableEq Result] {R : Register}
    (firstRecord : Original → FirstOutcome → Intermediate)
    (lastRecord : Intermediate → LastOutcome → Result)
    (firstOperator : Original → FirstOutcome → HilbertOperator R)
    (lastOperator : Intermediate → LastOutcome → HilbertOperator R)
    (densities : Original → HilbertOperator R) (feed : UnitaryOperator R) (result : Result) :
    (∑ middle, ∑ lastOutcome, if lastRecord middle lastOutcome = result then
      lastOperator middle lastOutcome *
        (∑ original, ∑ firstOutcome, if firstRecord original firstOutcome = middle then
          feedSandwich feed (firstOperator original firstOutcome) (densities original) else 0) *
        (lastOperator middle lastOutcome).conjTranspose else 0) =
      ∑ original, ∑ firstOutcome, ∑ lastOutcome,
        if lastRecord (firstRecord original firstOutcome) lastOutcome = result then
          feedKrausOperator (lastOperator (firstRecord original firstOutcome) lastOutcome)
              (firstOperator original firstOutcome) feed * densities original *
            (feedKrausOperator (lastOperator (firstRecord original firstOutcome) lastOutcome)
              (firstOperator original firstOutcome) feed).conjTranspose else 0 := by
  refine (composeRetainedBlocks (R := R) firstRecord lastRecord
    (fun original outcome =>
      feedSandwich feed (firstOperator original outcome) (densities original))
    lastOperator result).trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro firstOutcome _
  apply Finset.sum_congr rfl
  intro lastOutcome _
  by_cases selected : lastRecord (firstRecord original firstOutcome) lastOutcome = result
  · rw [if_pos selected, if_pos selected]
    exact feedKraus_sandwich _ _ _ _
  · rw [if_neg selected, if_neg selected]

private lemma feed_composed_retained_blocks
    {Original FirstOutcome Intermediate LastOutcome Result : Type}
    [Fintype Original] [Fintype FirstOutcome] [Fintype Intermediate]
    [Fintype LastOutcome] [Fintype Result] [DecidableEq Intermediate] [DecidableEq Result]
    {R : Register} (state : ExecutionState Original R) (current : ExecutionState Intermediate R)
    (last : ExecutionState Intermediate R → ExecutionState Result R)
    (firstRecord : Original → FirstOutcome → Intermediate)
    (lastRecord : Intermediate → LastOutcome → Result)
    (firstOperator : Original → FirstOutcome → HilbertOperator R)
    (lastOperator : Intermediate → LastOutcome → HilbertOperator R)
    (firstActual : ∀ result, (current.block result).matrix =
      ∑ original, ∑ outcome, if firstRecord original outcome = result then
        firstOperator original outcome * (state.block original).matrix *
          (firstOperator original outcome).conjTranspose else 0)
    (lastActual : ∀ incoming : ExecutionState Intermediate R, ∀ result,
      ((last incoming).block result).matrix =
        ∑ middle, ∑ outcome, if lastRecord middle outcome = result then
          lastOperator middle outcome * (incoming.block middle).matrix *
            (lastOperator middle outcome).conjTranspose else 0)
    (feed : UnitaryOperator R) (result : Result) :
    (((last (current.applyUnitary (fun _ => feed))).block result).matrix) =
      ∑ original, ∑ firstOutcome, ∑ lastOutcome,
        if lastRecord (firstRecord original firstOutcome) lastOutcome = result then
          feedKrausOperator (lastOperator (firstRecord original firstOutcome) lastOutcome)
              (firstOperator original firstOutcome) feed *
            (state.block original).matrix *
              (feedKrausOperator (lastOperator (firstRecord original firstOutcome) lastOutcome)
                (firstOperator original firstOutcome) feed).conjTranspose
        else 0 := by
  rw [lastActual]
  simp_rw [unitary_retained_blocks state current firstRecord firstOperator firstActual feed]
  exact feed_composed_sum firstRecord lastRecord firstOperator lastOperator
    (fun original => (state.block original).matrix) feed result

variable {gates : GateModel} {oracles : OracleModel}
  {ctx : RuntimeCtx .quantum} {operations : ClassicalOpModel}
  {services : ClassicalOracleModel} {FirstOutcome LastOutcome : Type}
  [Fintype FirstOutcome] [Fintype LastOutcome]
  {first last : Circuit (.quantum gates oracles operations services) ctx ctx true}
  {environment : (ExecutionModel.quantum gates oracles operations
    services).Environment}

/-- The real final factor reads the real first Store, with the mathematical feed between them. -/
def instrumentFeedOperator (head : Instrument first FirstOutcome environment)
    (tail : Instrument last LastOutcome environment) (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference)) (store : Store ctx)
    (firstOutcome : FirstOutcome) (lastOutcome : LastOutcome) :
    HilbertOperator (ctx.register.prod Reference) :=
  referenceLift Reference (tail.operator (head.record store firstOutcome).1 lastOutcome) *
    ((feed : HilbertOperator (ctx.register.prod Reference)) *
      referenceLift Reference (head.operator store firstOutcome))

/-- The exact intermediate Store connects the two actual instruments through the source feed. -/
lemma instrument_feed_blocks (head : Instrument first FirstOutcome environment)
    (tail : Instrument last LastOutcome environment) (Reference : Register)
    (feed : UnitaryOperator (ctx.register.prod Reference))
    {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (result : Store ctx × (services.HiddenState × ((History × first.Path) × last.Path))) :
    ((last.execute environment Reference
      ((first.execute environment Reference state).applyUnitary (fun _ => feed))
        ).block result).matrix =
      ∑ original : Store ctx × (services.HiddenState × History),
        ∑ firstOutcome : FirstOutcome, ∑ lastOutcome : LastOutcome,
          if retainedRecord (services := services) tail.record
              (retainedRecord (services := services) head.record original firstOutcome)
                lastOutcome = result then
            instrumentFeedOperator head tail Reference feed original.1
                firstOutcome lastOutcome *
              (state.block original).matrix *
                (instrumentFeedOperator head tail Reference feed original.1
                  firstOutcome lastOutcome).conjTranspose
          else 0 := by
  exact feed_composed_retained_blocks state (first.execute environment Reference state)
    (fun incoming => last.execute environment Reference incoming)
    (retainedRecord (services := services) head.record)
    (retainedRecord (services := services) tail.record)
    (fun original outcome => referenceLift Reference (head.operator original.1 outcome))
    (fun middle outcome => referenceLift Reference (tail.operator middle.1 outcome))
    (fun selected => (head.blocks Reference state selected).trans
      (sum_condition_decisions _ _ _ _))
    (fun incoming selected => (tail.blocks Reference incoming selected).trans
      (sum_condition_decisions _ _ _ _)) feed result

end

end QuantumAlg.Execution
