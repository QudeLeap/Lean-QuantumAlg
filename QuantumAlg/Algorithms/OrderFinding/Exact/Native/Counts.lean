/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Exact.Native.Endpoint
public import QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.Accounting.ClassicalWeight
public import QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Endpoint
import all QuantumAlg.Algorithms.OrderFinding.Exact.Native.Resources
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Resources
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Resources
import all QuantumAlg.Components.Classical.TerminalDecode.Retained
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.ClassicalWeight
import all QuantumAlg.Core.Base.Accounting.Weighted
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Actual source-query count of complete native exact decoding

The physical source sample invokes its declared modular-exponentiation oracle
once. The retained classical decoder adds no quantum query.
-/

namespace QuantumAlg.OrderFinding.Exact.NativeEndpoint

noncomputable section

private lemma decoder_oracleCount_zero (t width : Nat)
    (path : (decoderCode t width).Path) :
    ResourcePool.count (model := Sampling.Native.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((decoderCode t width).resourcePool path) = 0 := by
  have bounded := ResourcePool.le_iff_count.mp
    (ClassicalRoutines.TerminalDecode.terminalDecode_routine_pool_le
      (model := Sampling.Native.model t width)
      (samplePost t width) t .bigEndian (sampleInput t width)
      (resultKey t width) (resultFresh t width) path)
    (.oracle UnitarySource.Coordinate.ordinary :
      Resource.Event (Sampling.Native.model t width))
  have zero : ResourcePool.count (model := Sampling.Native.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((decoderCode t width).resourcePool path) ≤ 0 := by
    simpa [decoderCode, ClassicalRoutines.TerminalDecode.envelope,
      ClassicalRoutines.TerminalDecode.bitEnvelope,
      ClassicalRoutines.TerminalDecode.shiftEvent,
      ClassicalRoutines.TerminalDecode.incrementEvent] using bounded
  exact Nat.eq_zero_of_le_zero zero

/-- Every complete native exact sample invokes the declared source oracle once. -/
lemma code_modExpCount (t width : Nat)
    (path : (code t width).Path) :
    ResourcePool.count (model := Sampling.Native.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((code t width).resourcePool path) = 1 := by
  change (Circuit.seq (sampleCode t width) (decoderCode t width)).Path at path
  change ResourcePool.count (model := Sampling.Native.model t width)
    (.oracle UnitarySource.Coordinate.ordinary)
    (ResourcePool.ofList ((sampleCode t width).eventTrace path.1 ++
      (decoderCode t width).eventTrace path.2)) = 1
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count (model := Sampling.Native.model t width)
    (.oracle UnitarySource.Coordinate.ordinary)
      ((sampleCode t width).resourcePool path.1) +
    ResourcePool.count (model := Sampling.Native.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((decoderCode t width).resourcePool path.2) = 1
  have sampled :
      ResourcePool.count (model := Sampling.Native.model t width)
        (.oracle UnitarySource.Coordinate.ordinary)
        ((sampleCode t width).resourcePool path.1) = 1 :=
    Sampling.Native.Framed.code_modExpCount
      Sampling.Native.pre samplePreNoQuantum t width path.1
  rw [sampled, decoder_oracleCount_zero, Nat.add_zero]

/-- The public algorithm's same execution contains exactly one source query. -/
public lemma exactOrderFinding_algorithm_modExpCount (t width : Nat)
    (path : (algorithm t width).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((algorithm t width).run.code.resourcePool path) = 1 :=
  code_modExpCount t width path

/-- Exact native coordinates and the single source query belong to the complete
named execution, including its actual classical recovery tail. -/
public lemma exactOrderFinding_algorithm_nativeCounts (t width : Nat)
    (path : (algorithm t width).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.model t width) (.gate .singleQubit)
        ((algorithm t width).run.code.resourcePool path) = 2 * t + 3 * t.choose 2 ∧
    ResourcePool.count (model := Sampling.Native.model t width) (.gate .cnot)
        ((algorithm t width).run.code.resourcePool path) =
          2 * t.choose 2 + 3 * (t / 2) ∧
    ResourcePool.count (model := Sampling.Native.model t width) (.gate .toffoli)
        ((algorithm t width).run.code.resourcePool path) = 0 ∧
    ResourcePool.count (model := Sampling.Native.model t width)
        (.oracle UnitarySource.Coordinate.ordinary)
        ((algorithm t width).run.code.resourcePool path) = 1 ∧
    ResourcePool.count (model := Sampling.Native.model t width) (.measurement (2 : ℕ+))
        ((algorithm t width).run.code.resourcePool path) = t := by
  constructor
  · simpa [algorithm, run, Sampling.Native.eventBudget, Sampling.Native.unitaryBudget] using
      code_count_nonclassical t width path (.gate .singleQubit) (fun operation => by simp)
  constructor
  · simpa [algorithm, run, Sampling.Native.eventBudget, Sampling.Native.unitaryBudget] using
      code_count_nonclassical t width path (.gate .cnot) (fun operation => by simp)
  constructor
  · simpa [algorithm, run, Sampling.Native.eventBudget, Sampling.Native.unitaryBudget] using
      code_count_nonclassical t width path (.gate .toffoli) (fun operation => by simp)
  constructor
  · simpa [algorithm, run, Sampling.Native.eventBudget, Sampling.Native.unitaryBudget] using
      code_count_nonclassical t width path (.oracle UnitarySource.Coordinate.ordinary)
        (fun operation => by simp)
  simpa [algorithm, run, Sampling.Native.eventBudget, Sampling.Native.unitaryBudget] using
      code_count_nonclassical t width path (.measurement (2 : ℕ+)) (fun operation => by simp)
/-- The real sample packing and retained decoder have a linear native
classical-operation allowance on every complete execution path. -/
public lemma exactOrderFinding_algorithm_classicalOperations_le (t width : Nat)
    (path : (algorithm t width).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm t width).run.code.resourcePool path) ≤ 2 * t + 1 := by
  have allowance : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (eventBudget t width) = 2 * t + 1 := by
    simp [eventBudget, Sampling.Native.eventBudget,
      Sampling.Native.unitaryBudget, ClassicalRoutines.TerminalDecode.envelope,
      ClassicalRoutines.TerminalDecode.bitEnvelope,
      ClassicalRoutines.TerminalDecode.shiftEvent,
      ClassicalRoutines.TerminalDecode.incrementEvent, ResourcePool.scale,
      Resource.Event.classicalOperationWeight]
    omega
  exact (ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight
    (code_events_le t width path)).trans_eq allowance

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
