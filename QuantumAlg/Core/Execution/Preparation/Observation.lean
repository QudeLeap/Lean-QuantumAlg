/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Preparation.Laws
import all QuantumAlg.Core.Execution.Owned.ClassicalInputs
import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Preparation preserves old structural-input reference observations

The actual canonical zero preparation tensors the new systems beside the old
context-reference matrix. Tracing those new systems preserves every original
classical block and both reference coordinates. The actual owned-layout
store extension then transports the weight through its structural input lift.

These laws include arbitrary mixed states and all classical-reference
correlations. They neither release the newly prepared systems nor replace
their state with a separate probability model.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Execution

variable {ctx : RuntimeCtx .quantum} {systemCount : Nat} {Reference : Register}

/-- Normalized preparation retains every classical weight and complete reference entry. -/
theorem referenceFiberSum_prepareContext {C : Type} [Fintype C]
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (weight : C → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        (prepareContext state key layout fresh disjoint prepared)
        (fun value _ => weight value) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun value _ => weight value) leftRef rightRef := by
  have transported := (preparedLocalBasisEquiv ctx key layout fresh disjoint).sum_comp
    (fun basis => ∑ value : C, weight value *
      ((prepareContext state key layout fresh disjoint prepared).block value).matrix
        (basis, leftRef) (basis, rightRef))
  refine transported.symm.trans ?_
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro oldBasis _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro value _
  rw [← Finset.mul_sum]
  exact congrArg (fun entry : ℂ => weight value * entry)
    (prepareContext_old_block_marginal state key layout fresh disjoint prepared value
      (oldBasis, leftRef) (oldBasis, rightRef))

end Execution

namespace Circuit

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}

open Execution

variable {ctx : RuntimeCtx .quantum} {systemCount : Nat}

/-- Actual preparation observes the weight transported through its owned-layout store push. -/
theorem referenceFiberSum_execute_prepareZero
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (classicalOracles.HiddenState × History))
    (weight : Store (ctx.addOwnedLayout key layout fresh disjoint) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((Circuit.prepareZero (gates := gates) (oracles := oracles)
          (operations := operations) (classicalOracles := classicalOracles)
          ctx key layout fresh disjoint).execute Reference state)
        (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.pushOwnedLayout key layout fresh disjoint))
        leftRef rightRef := by
  rw [Circuit.execute_prepareZero]
  dsimp only [State.mapHistory, State.prepare]
  rw [ExecutionState.referenceFiberSum_mapClassical,
    ExecutionState.referenceFiberSum_mapClassical]
  exact referenceFiberSum_prepareContext state key layout fresh disjoint
    (BasisPreparation.zero layout).normalized
    (fun entry => weight (entry.1.pushOwnedLayout key layout fresh disjoint)) leftRef rightRef

/-- Every lifted earlier structural operand retains its full weighted reference observation. -/
theorem referenceFiberSum_execute_prepareZero_input {inputShape : CShape}
    (input : CInputRef ctx inputShape)
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (classicalOracles.HiddenState × History))
    (weight : inputShape.Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((Circuit.prepareZero (gates := gates) (oracles := oracles)
          (operations := operations) (classicalOracles := classicalOracles)
          ctx key layout fresh disjoint).execute Reference state)
        (fun entry _ => weight
          (entry.1.read (input.underOwnedLayout key layout fresh disjoint))) leftRef rightRef =
      ExecutionState.referenceFiberSum state (fun entry _ => weight (entry.1.read input))
        leftRef rightRef := by
  refine (referenceFiberSum_execute_prepareZero (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
    key layout fresh disjoint state
    (fun store => weight (store.read (input.underOwnedLayout key layout fresh disjoint)))
    leftRef rightRef).trans ?_
  exact congrArg
    (fun observe : (Store ctx × (classicalOracles.HiddenState × History)) →
        ctx.register.Index → ℂ =>
      ExecutionState.referenceFiberSum state observe leftRef rightRef)
    (funext fun entry => funext fun _ => congrArg weight
      (Store.read_pushOwnedLayout_underOwnedLayout entry.1 key layout fresh disjoint input))

end Circuit

end

end QuantumAlg
