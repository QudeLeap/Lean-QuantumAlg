/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# Weighted observations of complete basis-seeded store blocks

An actual state supported at one local basis value has the same complete
reference observation as the sum of its seed entries over real stores.
Summing an observed finite result's indicator fibers recovers its arbitrary
complex weight. Both identities concern the existing density blocks and
preserve the two reference coordinates separately.
-/

namespace QuantumAlg

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace ExecutionState

/-- Weighted finite indicator fibers are exactly the weight of the actual observation. -/
lemma referenceFiberSum_observation_fibers {C Outcome : Type}
    [Fintype C] [Fintype Outcome] {R Reference : Register}
    (state : ExecutionState C (Register.prod R Reference))
    (observe : C → R.Index → Outcome) (weight : Outcome → ℂ)
    (leftRef rightRef : Reference.Index) :
    (∑ outcome : Outcome, weight outcome *
      referenceFiberSum state
        (fun original basis => if observe original basis = outcome then 1 else 0)
        leftRef rightRef) =
      referenceFiberSum state (fun original basis => weight (observe original basis))
        leftRef rightRef := by
  unfold referenceFiberSum
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro basis _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

end ExecutionState

namespace Execution.BasisSeeded

/-- Actual complete-store weights need only the seed entry of each store-reference block. -/
lemma referenceFiberSum_seed {kind : ProblemKind} {ctx : RuntimeCtx kind}
    (seed : ctx.register.Index) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (seeded : Holds seed state)
    (weight : Store ctx → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) leftRef rightRef =
      ∑ original : Store ctx, weight original *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef) := by
  refine (fiber_store_blocks state (fun original _ => weight original) leftRef rightRef).trans ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [← Finset.mul_sum]
  exact congrArg (fun coefficient : ℂ => weight original * coefficient)
    (reference_entry seed state seeded original leftRef rightRef)

end Execution.BasisSeeded

end

end QuantumAlg
