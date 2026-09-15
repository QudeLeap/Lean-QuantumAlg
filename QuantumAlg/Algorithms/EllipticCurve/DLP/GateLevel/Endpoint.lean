/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Specification
import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Recovery.Probability
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Complete correctness of the original opaque ECDLP execution

The original secret is a proof witness for an accepted actual output. The
finite success bound, complete output, borrowed joint restoration and native
resource limits all concern the same reused-bank recovery run. No final
zero-state promise or implementation of the opaque group action is required.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelEndpoint

open Execution GateLevelAttempt.Native

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

private theorem accepted_atom_le_relational {kind : ProblemKind}
    {pre post : RuntimeCtx kind} {shape : CShape} (run : AlgorithmRun pre post shape)
    {Reference : Register} (original : Input pre Reference) (accepts : shape.Value → Prop)
    (value : shape.Value) (accepted : accepts value) :
    run.outputDistribution original value ≤
      (run.relationalDistribution original).toOuterMeasure {pair | accepts pair.2} := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  simp only [AlgorithmRun.outputDistribution, AlgorithmRun.relationalDistribution,
    PMF.toOuterMeasure_map_apply]
  apply (run.executionDistribution original).toOuterMeasure_mono
  intro record member
  change accepts (run.result record)
  rw [member.1]
  exact accepted

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}

private theorem secret_is_accepted (I : ECDLPInstance E) :
    Specification.accepts I
      (.optionSome (CShape.wordOfNat (FiniteCyclicDLP.orderWidth (problem I))
        (input I).secret.val)) := by
  let : NeZero I.subgroupOrder := ⟨Nat.ne_of_gt I.subgroupOrder_pos⟩
  have fits : (input I).secret.val < 2 ^ FiniteCyclicDLP.orderWidth (problem I) :=
    lt_of_lt_of_le (FiniteCyclicDLP.Probability.residueIndex (problem I) (input I).secret).isLt
      (FiniteCyclicDLP.order_le_fourierModulus (problem I))
  refine ⟨_, rfl, ?_⟩
  change I.CandidateScalar
    (((input I).secret.val % 2 ^ FiniteCyclicDLP.orderWidth (problem I) : Nat) :
      ZMod I.subgroupOrder)
  rw [Nat.mod_eq_of_lt fits]
  change I.CandidateScalar ((secret I).val : ZMod I.subgroupOrder)
  rw [ZMod.natCast_zmod_val]
  exact secret_spec I

/-- The actual opaque sampling and checked recovery run solves the independent original domain. -/
theorem nativeECDLP_recovery_solves
    (I : ECDLPInstance E) (B : OrderExpansion (problem I).order) (A : Access I)
    (budget : Factoring.FailureBudget) (wellFormed : budget.WellFormed) :
    ({ run := recoveryRun (Runtime.Context.pre I)
        (PublicInput.nativeECDLP_input_quantumWires I) I B A (retryCountForBudget I budget)
        (Runtime.Context.baseRef I) (Runtime.Context.targetRef I) } :
      Algorithm .quantum (Specification.inputContext I) (Specification.outputContext I)
        (.option (.unsignedWord (FiniteCyclicDLP.orderWidth (problem I))))).Solves
          (Specification.specification I B budget wellFormed) where
  success := by
    intro Reference original valid
    exact (nativeECDLP_recoveryRun_calibrated_success I B A budget wellFormed original valid).trans
      (accepted_atom_le_relational _ original (Specification.accepts I) _ (secret_is_accepted I))
  states := by
    intro Reference original valid requirement member
    cases member
  borrowed := by
    intro Reference original valid
    exact Circuit.borrowedRestored_of_noBorrowedQuantum _
      (PublicInput.nativeECDLP_input_noBorrowedQuantum I) Reference
      (original.state.mapClassical (fun store => (store, store)))
  events := by
    intro Reference original valid path supported
    exact (Specification.nativeECDLP_recovery_closedResourceContract I B A budget).events path
  resident := by
    intro Reference original valid path supported
    exact (Specification.nativeECDLP_recovery_closedResourceContract I B A budget).resident path
  auxiliary := by
    intro Reference original valid path supported
    exact (Specification.nativeECDLP_recovery_closedResourceContract I B A budget).auxiliary path
  depth := by
    intro Reference original valid path supported
    exact (Specification.nativeECDLP_recovery_closedResourceContract I B A budget).depth path

end

end GateLevelEndpoint
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
