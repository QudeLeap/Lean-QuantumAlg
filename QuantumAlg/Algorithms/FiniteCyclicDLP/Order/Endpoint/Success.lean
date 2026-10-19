/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Amplification
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Distribution
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Values

/-!
# Two-thirds success of the all-positive-order finite-cyclic DLP endpoint

Order one returns its unique residue with certainty.  Every larger positive
order uses the selected Fourier-family event, the conservative retry count,
and the actual checked first-success recovery value.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderEndpoint

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- The independent endpoint law returns the advertised discrete logarithm
with probability at least two thirds for every positive order. -/
public lemma outputLaw_success (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      outputLaw P
        (.optionSome
          (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)) := by
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  by_cases trivial : P.order = 1
  · have secretZero : secret.secret.val = 0 := by
      have bound := ZMod.val_lt secret.secret
      omega
    have constant : recoveredOutcome P = Function.const
        (List.Vector
          (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) (sampleCount P))
        (.optionSome
          (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)) := by
      funext outcomes
      rw [recoveredOutcome_eq, recoveredValue_order_one P trivial, secretZero]
      rfl
    rw [outputLaw_eq, constant, PMF.map_const]
    norm_num
  · rw [← PMF.toOuterMeasure_apply_singleton, outputLaw_eq,
      PMF.toOuterMeasure_map_apply]
    refine (OrderAmplification.selected_vector_probability P
      (OrderExecution.canonicalExpansion P) secret).trans
      (MeasureTheory.measure_mono ?_)
    intro outcomes selected
    change recoveredOutcome P outcomes = .optionSome
      (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)
    rw [recoveredOutcome_eq, recoveredValue_nontrivial P trivial]
    exact OrderRecovery.Native.recoveryValue_selected_samples P secret
      (recoverySpec P trivial) (by
        unfold recoverySpec FiniteCyclicDLP.Canonical.resourceModulusSpec
        rfl)
      (sampleCount P) outcomes selected

/-- Once the actual batch has its trace-derived independent law, the complete
run meets the same two-thirds threshold without any extra runtime promise. -/
public lemma run_success_of_batch (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P)
    {Reference : Register}
    (input : OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference)
    (batchLaw :
      ((OrderBatch.run P (sampleCount P)
        (OrderExecution.canonicalExpansion P)).outputDistribution
          (OrderExecution.sourceEnvironment P) input).map
          (OrderBatch.observedVector P (sampleCount P)) =
        PMF.independentReplicateVector
          (OrderBornBridge.outcomePMF P (OrderExecution.canonicalExpansion P))
          (sampleCount P)) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      (run P).outputDistribution (OrderExecution.sourceEnvironment P) input
        (.optionSome
          (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)) := by
  rw [run_outputDistribution_of_batch P input batchLaw]
  exact outputLaw_success P secret

/-- The actual all-positive-order finite-cyclic DLP run succeeds with
probability at least two thirds. -/
public lemma run_success (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P)
    {Reference : Register}
    (input : OracleInput (OrderExecution.model P).classicalOracles
      OrderExecution.pre Reference) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      (run P).outputDistribution (OrderExecution.sourceEnvironment P) input
        (.optionSome
          (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)) := by
  rw [run_outputDistribution P input]
  exact outputLaw_success P secret

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
