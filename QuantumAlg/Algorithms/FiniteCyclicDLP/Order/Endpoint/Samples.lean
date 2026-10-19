/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Observation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Observation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution.Probability
import all QuantumAlg.Core.Base.Classical.Value

/-!
# Value-level inverse of the native-dimensional retained sample readout

This inverse concerns only the finite value carrier of the retained measurement
cells.  It adds no packing instruction, storage cell or resource event.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- An ordered terminal bit string determines every corresponding two-valued cell. -/
public def rawSample (P : KnownOrderProblem G)
    (outcome : TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) :
    CShape.Value (.fixedVector (OrderExecution.sampleWidth P) (.finite 2)) :=
  .fixedVector fun index => .finite (if outcome index then 1 else 0)

omit [Fintype G] in
/-- Reading the inverse sample recovers exactly the supplied terminal bit string. -/
public lemma observed_rawSample (P : KnownOrderProblem G)
    (outcome : TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) :
    OrderExecution.observedOutcome P (rawSample P outcome) = outcome := by
  funext index
  cases value : outcome index <;>
    simp only [OrderExecution.observedOutcome, rawSample, CShape.Value.get,
      CShape.Value.toFin, value, Bool.false_eq_true, if_false, if_true]
  all_goals rfl

omit [Fintype G] in
/-- Every actual finite sample is reconstructed from its observed terminal bits. -/
public lemma rawSample_observed (P : KnownOrderProblem G)
    (value : CShape.Value (.fixedVector (OrderExecution.sampleWidth P) (.finite 2))) :
    rawSample P (OrderExecution.observedOutcome P value) = value := by
  cases value with
  | fixedVector values =>
      dsimp only [rawSample]
      congr 1
      funext index
      cases observed : values index with
      | finite number =>
          fin_cases number <;>
            simp only [OrderExecution.observedOutcome, CShape.Value.get,
              CShape.Value.toFin, observed]
          all_goals rfl

/-- A fixed-length outcome vector determines the complete retained sample value. -/
@[expose] public def rawSamples (P : KnownOrderProblem G) (count : Nat)
    (outcomes : List.Vector
      (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) count) :
    CShape.Value (.fixedVector count
      (.fixedVector (OrderExecution.sampleWidth P) (.finite 2))) :=
  .fixedVector fun index => rawSample P (outcomes.get index)

omit [Fintype G] in
@[simp] public lemma rawSamples_get (P : KnownOrderProblem G) (count : Nat)
    (outcomes : List.Vector
      (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) count)
    (index : Fin count) :
    (rawSamples P count outcomes).get index = rawSample P (outcomes.get index) := by
  simp only [rawSamples, CShape.Value.get]

omit [Fintype G] in
/-- Complete vector observation is inverse to value-level reconstruction. -/
public lemma observed_rawSamples (P : KnownOrderProblem G) (count : Nat)
    (outcomes : List.Vector
      (TerminalZMeasure.Outcome (OrderExecution.sampleWidth P)) count) :
    OrderBatch.observedVector P count (rawSamples P count outcomes) = outcomes := by
  apply List.Vector.ext
  intro index
  simp only [OrderBatch.observedVector, List.Vector.get_ofFn,
    rawSamples, CShape.Value.get, observed_rawSample]

omit [Fintype G] in
/-- Value-level reconstruction preserves every retained finite cell. -/
public lemma rawSamples_observed (P : KnownOrderProblem G) (count : Nat)
    (value : CShape.Value (.fixedVector count
      (.fixedVector (OrderExecution.sampleWidth P) (.finite 2)))) :
    rawSamples P count (OrderBatch.observedVector P count value) = value := by
  cases value with
  | fixedVector values =>
      dsimp only [rawSamples]
      congr 1
      funext index
      simpa only [OrderBatch.observedVector, List.Vector.get_ofFn,
        CShape.Value.get] using rawSample_observed P (values index)

end

end QuantumAlg.FiniteCyclicDLP.OrderEndpoint
