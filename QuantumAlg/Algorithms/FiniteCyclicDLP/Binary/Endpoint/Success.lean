/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Probability
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Endpoint.Distribution
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Recovery.Native.Selection.Values

/-!
# Two-thirds success of the all-positive-order finite-cyclic DLP endpoint

Order one returns its unique residue with certainty.  Every larger positive
order uses the selected Fourier-family event, the full-family retry count,
and the actual checked first-success recovery value. The original input domain
and trivial group case are preserved [Sho95, source.tex:1841-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

universe u

variable {G : Type u} [Group G] [Fintype G]

omit [Fintype G] in
/-- The independent endpoint law returns the advertised discrete logarithm
with probability at least two thirds for every positive order. -/
public lemma binaryEndpoint_outputLaw_success (P : KnownOrderProblem G)
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
          (TerminalZMeasure.Outcome (Reusable.sampleWidth P)) (sampleCount P))
        (.optionSome
          (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)) := by
      funext outcomes
      rw [binaryEndpoint_recoveredOutcome_eq, binaryEndpoint_recoveredValue_order_one P
        trivial, secretZero]
      rfl
    rw [binaryEndpoint_outputLaw_eq, constant, PMF.map_const]
    norm_num
  · rw [← PMF.toOuterMeasure_apply_singleton, binaryEndpoint_outputLaw_eq,
      PMF.toOuterMeasure_map_apply]
    refine (Binary.binary_selected_vector_probability P
      (OrderExecution.canonicalExpansion P) secret).trans
      (MeasureTheory.measure_mono ?_)
    intro outcomes selected
    change recoveredOutcome P outcomes = .optionSome
      (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)
    rw [binaryEndpoint_recoveredOutcome_eq, binaryEndpoint_recoveredValue_nontrivial P trivial]
    exact OrderRecovery.Native.recoveryValue_selected_samples P secret
      (recoverySpec P trivial) (by
        unfold recoverySpec FiniteCyclicDLP.Canonical.resourceModulusSpec
        rfl)
      (sampleCount P) outcomes selected

/-- Once the actual batch has its trace-derived independent law, the complete
run meets the same two-thirds threshold without any extra runtime promise. -/
public lemma binaryEndpoint_run_success_of_batch (P : KnownOrderProblem G)
    (secret : FiniteCyclicDLP.Input P)
    {Reference : Register}
    (input : OracleInput (Reusable.model P).classicalOracles
      Reusable.pre Reference)
    (batchLaw :
      ((Reusable.run P (sampleCount P)
        (OrderExecution.canonicalExpansion P)).outputDistribution
          (Reusable.sourceEnvironment P) input).map
          (Reusable.observedVector P (sampleCount P)) =
        PMF.independentReplicateVector
          (Binary.outcomePMF P (OrderExecution.canonicalExpansion P))
          (sampleCount P)) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      (run P).outputDistribution (Reusable.sourceEnvironment P) input
        (.optionSome
          (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)) := by
  rw [binaryEndpoint_run_outputDistribution_of_batch P input batchLaw]
  exact binaryEndpoint_outputLaw_success P secret

/-- The same actual binary, sequential, measured and reset full run succeeds with probability
  two thirds. -/
public lemma binaryEndpoint_run_success (P : KnownOrderProblem G) (secret :
  FiniteCyclicDLP.Input P)
    {Reference : Register}
    (input : OracleInput (Reusable.model P).classicalOracles Reusable.pre Reference) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      (run P).outputDistribution (Reusable.sourceEnvironment P) input
        (.optionSome
          (CShape.wordOfNat (OrderPreparation.width P) secret.secret.val)) := by
  rw [binaryEndpoint_run_outputDistribution]
  exact binaryEndpoint_outputLaw_success P secret

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
