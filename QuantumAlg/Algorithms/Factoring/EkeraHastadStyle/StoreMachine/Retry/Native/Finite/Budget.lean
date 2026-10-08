/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Endpoint
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Finite.Endpoint
import all QuantumAlg.Core.Algorithm.Solves.Budget

/-!
# Scalar specialization of the complete native retry contract

The independent space and depth ceilings are transported before fixing the
batch count. This retains the complete actual execution and every state and
success obligation without expanding a fixed-size dependent path tree.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) {N : Nat}

/-- The same factoring contract with independently supplied space and serial-depth ceilings. -/
@[expose] public def budgetedProblem (model : GoodKeyModel N) (count : Nat)
    (space : SpacePool .quantum) (serialDepth : Nat) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model) base
      (context base noQuantum N count) (LatticeBatchRecoveryOutput.OutputShape N) :=
  { fixedRoundProblem base noQuantum model count with
    resources :=
      { events := eventEnvelope N count
        resident := base.residentSpace + space
        auxiliary := base.auxiliarySpace + space }
    depth :=
      { duration := fun _ => 1
        limit := serialDepth
        classicalQuery_unit := fun _ => rfl
        quantumQuery_unit := fun _ => rfl } }

/-- Independent scalar comparisons suffice for the full same-execution specification. -/
theorem algorithm_solves_budgeted (model : GoodKeyModel N) (count : Nat)
    (space : SpacePool .quantum) (serialDepth : Nat)
    (spaceBound : additionalSpace N count ≤ space)
    (depthBound : NativeFiniteRetry.depthBound N count ≤ serialDepth) :
    Algorithm.Solves (algorithm base noQuantum model.input count)
      (budgetedProblem base noQuantum model count space serialDepth) := by
  apply Algorithm.Solves.enlargeBudgets
    (algorithm_solves_fixedRound base noQuantum model count)
    (budgetedProblem base noQuantum model count space serialDepth).resources
    (budgetedProblem base noQuantum model count space serialDepth).depth
  · exact le_rfl
  · exact fun axis => Nat.add_le_add_left (spaceBound axis) _
  · exact fun axis => Nat.add_le_add_left (spaceBound axis) _
  · rfl
  · exact depthBound

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeFiniteRetry
