/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback.Matrix
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Instrument

/-!
# Actual complete earlier-window feedback word

The extracted operators follow the exact executed list order. Each factor
reads the same original stored cell as its real guarded branch. Exact stored
density equations compose those instructions without dropping History or
Reference, and feed the same corrected measured readout instrument.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback

noncomputable section

open Execution
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

def atOperator (ports : Ports ctx totalBits active) (current : Fin active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) (stored : Store ctx) :
    List (BitPosition totalBits) → HilbertOperator (ctx.register.prod Reference)
  | [] => 1
  | previous :: rest => atOperator ports current environment Reference stored rest *
      oneOperator ports previous current environment Reference stored

def atScalar (ports : Ports ctx totalBits active) (current : Fin active) (stored : Store ctx)
    (basis : ctx.register.Index) : List (BitPosition totalBits) → Complex
  | [] => 1
  | previous :: rest => atScalar ports current stored basis rest *
      oneScalar ports previous current stored basis

def wordOperator (ports : Ports ctx totalBits active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) (stored : Store ctx) :
    List (Fin active) → HilbertOperator (ctx.register.prod Reference)
  | [] => 1
  | current :: rest => wordOperator ports environment Reference stored rest *
      atOperator ports current environment Reference stored (previousPositions totalBits)

def wordScalar (ports : Ports ctx totalBits active) (stored : Store ctx)
    (basis : ctx.register.Index) : List (Fin active) → Complex
  | [] => 1
  | current :: rest => wordScalar ports stored basis rest *
      atScalar ports current stored basis (previousPositions totalBits)

lemma atOperator_diagonal (ports : Ports ctx totalBits active) (current : Fin active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) (stored : Store ctx)
    (previous : List (BitPosition totalBits)) :
    atOperator ports current environment Reference stored previous =
      Matrix.diagonal (fun basis => atScalar ports current stored basis.1 previous) := by
  induction previous with
  | nil =>
      ext row column
      simp only [atOperator, atScalar, Matrix.one_apply, Matrix.diagonal_apply]
  | cons previous rest ih =>
      rw [atOperator, ih, oneOperator_diagonal, Matrix.diagonal_mul_diagonal]
      rfl

lemma wordOperator_diagonal (ports : Ports ctx totalBits active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) (stored : Store ctx)
    (current : List (Fin active)) :
    wordOperator ports environment Reference stored current =
      Matrix.diagonal (fun basis => wordScalar ports stored basis.1 current) := by
  induction current with
  | nil =>
      ext row column
      simp only [wordOperator, wordScalar, Matrix.one_apply, Matrix.diagonal_apply]
  | cons current rest ih =>
      rw [wordOperator, ih, atOperator_diagonal, Matrix.diagonal_mul_diagonal]
      rfl

/-- Every real earlier-result branch acts on its same complete original stored block. -/
lemma feedbackAt_store_matrix (ports : Ports ctx totalBits active) (current : Fin active)
    (previous : List (BitPosition totalBits))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (((feedbackAt ports current previous).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      atOperator ports current environment.quantum Reference stored previous *
        (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix *
          (atOperator ports current environment.quantum Reference stored
            previous).conjTranspose := by
  induction previous generalizing History with
  | nil =>
      rw [feedbackAt, identity_store_matrix]
      simp only [atOperator, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  | cons previous rest ih =>
      refine (congrArg DensityOperator.matrix
        (Circuit.seq_store_marginal (one ports previous current) (feedbackAt ports current rest)
          environment state stored)).trans ?_
      refine (ih ((one ports previous current).execute environment Reference state)).trans ?_
      refine (congrArg
        (fun density : HilbertOperator (ctx.register.prod Reference) =>
          atOperator ports current environment.quantum Reference stored rest * density *
            (atOperator ports current environment.quantum Reference stored rest).conjTranspose)
        (one_store_matrix ports previous current environment state stored)).trans ?_
      simp only [atOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The literal all-current-wire feedback prefix retains every complete original store. -/
lemma priorFeedback_store_matrix (ports : Ports ctx totalBits active)
    (current : List (Fin active))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (((priorFeedback ports current).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      wordOperator ports environment.quantum Reference stored current *
        (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix *
          (wordOperator ports environment.quantum Reference stored current).conjTranspose := by
  induction current generalizing History with
  | nil =>
      rw [priorFeedback, identity_store_matrix]
      simp only [wordOperator, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  | cons current rest ih =>
      refine (congrArg DensityOperator.matrix
        (Circuit.seq_store_marginal (feedbackAt ports current (previousPositions totalBits))
          (priorFeedback ports rest) environment state stored)).trans ?_
      refine (ih ((feedbackAt ports current (previousPositions totalBits)).execute
        environment Reference state)).trans ?_
      refine (congrArg
        (fun density : HilbertOperator (ctx.register.prod Reference) =>
          wordOperator ports environment.quantum Reference stored rest * density *
            (wordOperator ports environment.quantum Reference stored rest).conjTranspose)
        (feedbackAt_store_matrix ports current (previousPositions totalBits)
          environment state stored)).trans ?_
      simp only [wordOperator, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Complete actual window instrument includes its real same-stream earlier-cell phase word. -/
lemma inverseCode_instrument_store_matrix (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx) :
    (((inverseCode ports).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store ctx, ∑ outcome : Bits active,
        if outcomeStore active ports original outcome = stored then
          (outcomeKraus environment.quantum Reference active ports outcome *
              wordOperator ports environment.quantum Reference original (List.finRange active)) *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              (outcomeKraus environment.quantum Reference active ports outcome *
                wordOperator ports environment.quantum Reference original
                  (List.finRange active)).conjTranspose
        else 0 := by
  rw [window_inverseCode_store, window_readout_instrument_store_matrix]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases written : outcomeStore active ports original outcome = stored
  · simp only [if_pos written]
    refine (congrArg
      (fun density : HilbertOperator (ctx.register.prod Reference) =>
        outcomeKraus environment.quantum Reference active ports outcome * density *
          (outcomeKraus environment.quantum Reference active ports outcome).conjTranspose)
      (priorFeedback_store_matrix ports (List.finRange active) environment state original)).trans ?_
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · simp only [if_neg written]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback
