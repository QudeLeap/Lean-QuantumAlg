/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Endpoint.Samples
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Readout
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.Observation
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Execution.Probability
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Reusable.Readout

/-!
# Value-level decoding of sequential finite-cyclic samples

This reuses the exact finite-cell inverse of the earlier implementation. It
only compares values; it adds no packing gate, physical wire or allocation.
The actual samples are written by the reusable binary sampler.
-/

namespace QuantumAlg.FiniteCyclicDLP.BinaryEndpoint

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Reconstruct the retained cells from their ordered measured bits. -/
public abbrev rawSamples (P : KnownOrderProblem G) (count : Nat)
    (outcomes : List.Vector
      (TerminalZMeasure.Outcome (Reusable.sampleWidth P)) count) :
    CShape.Value (.fixedVector count
      (.fixedVector (Reusable.sampleWidth P) (.finite 2))) :=
  OrderEndpoint.rawSamples P count outcomes

/-- The unchanged two-valued decoder reconstructs every complete retained vector. -/
public lemma binaryEndpoint_rawSamples_observed (P : KnownOrderProblem G) (count : Nat)
    (value : CShape.Value (.fixedVector count
      (.fixedVector (Reusable.sampleWidth P) (.finite 2)))) :
    rawSamples P count (Reusable.observedVector P count value) = value := by
  exact OrderEndpoint.rawSamples_observed P count value

/-- The value-level inverse returns every measured bit in chronological order. -/
public lemma binaryEndpoint_observed_rawSamples (P : KnownOrderProblem G) (count : Nat)
    (outcomes : List.Vector
      (TerminalZMeasure.Outcome (Reusable.sampleWidth P)) count) :
    Reusable.observedVector P count (rawSamples P count outcomes) = outcomes := by
  exact OrderEndpoint.observed_rawSamples P count outcomes

end

end QuantumAlg.FiniteCyclicDLP.BinaryEndpoint
