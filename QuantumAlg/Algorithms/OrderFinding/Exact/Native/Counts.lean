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

private theorem decoder_oracleCount_zero {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (decoderCode access).Path) :
    ResourcePool.count (model := Sampling.Native.model access)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((decoderCode access).resourcePool path) = 0 := by
  have bounded := ResourcePool.le_iff_count.mp
    (ClassicalRoutines.TerminalDecode.terminalDecode_routine_pool_le
      (model := Sampling.Native.model access)
      (samplePost t width) t .bigEndian (sampleInput t width)
      (resultKey t width) (resultFresh t width) path)
    (.oracle UnitarySource.Coordinate.ordinary :
      Resource.Event (Sampling.Native.model access))
  have zero : ResourcePool.count (model := Sampling.Native.model access)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((decoderCode access).resourcePool path) ≤ 0 := by
    simpa [decoderCode, ClassicalRoutines.TerminalDecode.envelope,
      ClassicalRoutines.TerminalDecode.bitEnvelope,
      ClassicalRoutines.TerminalDecode.shiftEvent,
      ClassicalRoutines.TerminalDecode.incrementEvent] using bounded
  exact Nat.eq_zero_of_le_zero zero

/-- Every complete native exact sample invokes the declared source oracle once. -/
theorem code_modExpCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (code access).Path) :
    ResourcePool.count (model := Sampling.Native.model access)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((code access).resourcePool path) = 1 := by
  change (Circuit.seq (sampleCode access) (decoderCode access)).Path at path
  change ResourcePool.count (model := Sampling.Native.model access)
    (.oracle UnitarySource.Coordinate.ordinary)
    (ResourcePool.ofList ((sampleCode access).eventTrace path.1 ++
      (decoderCode access).eventTrace path.2)) = 1
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count (model := Sampling.Native.model access)
    (.oracle UnitarySource.Coordinate.ordinary)
      ((sampleCode access).resourcePool path.1) +
    ResourcePool.count (model := Sampling.Native.model access)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((decoderCode access).resourcePool path.2) = 1
  have sampled :
      ResourcePool.count (model := Sampling.Native.model access)
        (.oracle UnitarySource.Coordinate.ordinary)
        ((sampleCode access).resourcePool path.1) = 1 :=
    Sampling.Native.Framed.code_modExpCount
      Sampling.Native.pre samplePreNoQuantum access path.1
  rw [sampled, decoder_oracleCount_zero, Nat.add_zero]

/-- The public algorithm's same execution contains exactly one source query. -/
public theorem exactOrderFinding_algorithm_modExpCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (algorithm access).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.model access)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((algorithm access).run.code.resourcePool path) = 1 :=
  code_modExpCount access path

/-- Exact native coordinates and the single source query belong to the complete
named execution, including its actual classical recovery tail. -/
public theorem exactOrderFinding_algorithm_nativeCounts {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (algorithm access).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.model access) (.gate .singleQubit)
        ((algorithm access).run.code.resourcePool path) = 2 * t + 3 * t.choose 2 ∧
    ResourcePool.count (model := Sampling.Native.model access) (.gate .cnot)
        ((algorithm access).run.code.resourcePool path) =
          2 * t.choose 2 + 3 * (t / 2) ∧
    ResourcePool.count (model := Sampling.Native.model access) (.gate .toffoli)
        ((algorithm access).run.code.resourcePool path) = 0 ∧
    ResourcePool.count (model := Sampling.Native.model access)
        (.oracle UnitarySource.Coordinate.ordinary)
        ((algorithm access).run.code.resourcePool path) = 1 ∧
    ResourcePool.count (model := Sampling.Native.model access) (.measurement (2 : ℕ+))
        ((algorithm access).run.code.resourcePool path) = t := by
  constructor
  · simpa [algorithm, run, Sampling.Native.eventBudget, Sampling.Native.unitaryBudget] using
      code_count_nonclassical access path (.gate .singleQubit) (fun operation => by simp)
  constructor
  · simpa [algorithm, run, Sampling.Native.eventBudget, Sampling.Native.unitaryBudget] using
      code_count_nonclassical access path (.gate .cnot) (fun operation => by simp)
  constructor
  · simpa [algorithm, run, Sampling.Native.eventBudget, Sampling.Native.unitaryBudget] using
      code_count_nonclassical access path (.gate .toffoli) (fun operation => by simp)
  constructor
  · simpa [algorithm, run, Sampling.Native.eventBudget, Sampling.Native.unitaryBudget] using
      code_count_nonclassical access path (.oracle UnitarySource.Coordinate.ordinary)
        (fun operation => by simp)
  simpa [algorithm, run, Sampling.Native.eventBudget, Sampling.Native.unitaryBudget] using
      code_count_nonclassical access path (.measurement (2 : ℕ+)) (fun operation => by simp)
/-- The real sample packing and retained decoder have a linear native
classical-operation allowance on every complete execution path. -/
public theorem exactOrderFinding_algorithm_classicalOperations_le {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    (path : (algorithm access).run.code.Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((algorithm access).run.code.resourcePool path) ≤ 2 * t + 1 := by
  have allowance : ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      (eventBudget access) = 2 * t + 1 := by
    simp [eventBudget, Sampling.Native.eventBudget,
      Sampling.Native.unitaryBudget, ClassicalRoutines.TerminalDecode.envelope,
      ClassicalRoutines.TerminalDecode.bitEnvelope,
      ClassicalRoutines.TerminalDecode.shiftEvent,
      ClassicalRoutines.TerminalDecode.incrementEvent, ResourcePool.scale,
      Resource.Event.classicalOperationWeight]
    omega
  exact (ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight
    (code_events_le access path)).trans_eq allowance

end

end QuantumAlg.OrderFinding.Exact.NativeEndpoint
