/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Probability
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# Complete seed and reference state of every actual retry output

The actual first preparation and every later reset establish the same bank
seed. Its complete store blocks and the exact factor-vector reference law
give every observed output's full joint density, including empty factors
and zero-probability vectors. No caller seed or independence premise occurs.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution ShortDLP.CompiledMAU

local instance {α : Type} : DecidableEq α := Classical.decEq α

attribute [local irreducible] ExecutionState.referenceFiberSum

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (N count : Nat)

/-- The original bank seed on the actual final physical coordinates, after every measured batch. -/
def restoredSeed : (context base noQuantum N count).register.Index :=
  (RuntimePlacement.basisEquiv (shortLogBits N) (tradeoffBits N) (arithmeticBits N)
    (sameWires base noQuantum N count)).symm
    (ShortDLP.CompiledMAU.reloadLabel (shortLogBits N) (tradeoffBits N) (arithmeticBits N) N)

/-- Every actual vector block is its original probability times the full seed-reference target. -/
lemma output_joint_entry (specification : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (selected : (CShape.fixedVector (count + 1)
      (LatticeBatchRecoveryOutput.OutputShape N)).Value)
    (left right : (context base noQuantum N count).register.Index)
    (leftRef rightRef : Reference.Index) :
    ((((code base noQuantum specification count).execute environment Reference state).mapClassical
      (fun entry => (run base noQuantum specification count).output.eval entry.1)).block
        selected).matrix (left, leftRef) (right, rightRef) =
      if left = restoredSeed base noQuantum N count ∧
          right = restoredSeed base noQuantum N count then
        ((((PMF.independentReplicateVector
          ((sampledBatchOutputPMF specification).map LatticeBatchRecoveryOutput.outputValue)
          (count + 1)).map (fun values => CShape.Value.fixedVector values.get))
            selected).toReal : ℂ) * state.referenceMarginal.matrix leftRef rightRef
      else 0 := by
  have observed := BasisSeeded.readout_entry (restoredSeed base noQuantum N count)
    ((code base noQuantum specification count).execute environment Reference state)
    (code_seedBlocks base noQuantum specification count state)
    (fun store => (run base noQuantum specification count).output.eval store) selected
    left right leftRef rightRef
  have actual := code_weighted_reference (environment := environment)
    base noQuantum specification count state
    (fun value => if value = selected then 1 else 0) leftRef rightRef
  have scalar := actual.trans (by
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact ExecutionState.referenceFiberSum_constant_eq state _ leftRef rightRef)
  exact observed.trans (congrArg (fun coefficient : ℂ =>
    if left = restoredSeed base noQuantum N count ∧ right = restoredSeed base noQuantum N count
      then coefficient else 0) scalar)

/-- The complete mixed seed-reference promise includes unsupported observed factor vectors. -/
lemma output_statePromise (specification : Input N)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (normalized : state.IsNormalized)
    (selected : (CShape.fixedVector (count + 1)
      (LatticeBatchRecoveryOutput.OutputShape N)).Value) :
    (StatePromise.mixed
      (BasisReference.target (restoredSeed base noQuantum N count) state.referenceMarginal)
      (BasisReference.target_normalized (restoredSeed base noQuantum N count)
        state.referenceMarginal
        ((ExecutionState.referenceMarginal_mass state).trans normalized))).Holds
      ((((code base noQuantum specification count).execute environment Reference state).mapClassical
        (fun entry => (run base noQuantum specification count).output.eval entry.1)).block
          selected) :=
  BasisReference.promise_of_entries (restoredSeed base noQuantum N count) state.referenceMarginal
    ((ExecutionState.referenceMarginal_mass state).trans normalized) _
    ((((PMF.independentReplicateVector
      ((sampledBatchOutputPMF specification).map LatticeBatchRecoveryOutput.outputValue)
      (count + 1)).map (fun values => CShape.Value.fixedVector values.get)) selected).toReal)
    (output_joint_entry base noQuantum N count specification state selected)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRetryChain
