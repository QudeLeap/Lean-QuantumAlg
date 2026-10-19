/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Endpoint
public import QuantumAlg.Util.Order.Finding
public import QuantumAlg.Algorithms.OrderFinding.Oracle
public import QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Endpoint
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native.Counts
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Budget
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Resources
import all QuantumAlg.Components.Classical.Modular.NativePower.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Components.Classical.TerminalDecode.Resources
import all QuantumAlg.Core.Execution.Trace

/-!
# Actual source-query count of general native order finding

The framed source sample makes one declared modular-exponentiation call. The
retained continued-fraction recovery is entirely selected classical execution.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

private lemma recovery_oracleCount_zero {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (path : (recoveryCode spec t).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((recoveryCode spec t).resourcePool path) = 0 := by
  have bounded := ResourcePool.le_iff_count.mp
    (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_pool_le
      (model := Sampling.Native.Framed.model t width)
      (⟨spec⟩ : ClassicalAlgorithms.OrderRecovery.Spec width t) (baseInput t width) (sampleInput t
        width)
      (resultRef t width) path)
    (.oracle UnitarySource.Coordinate.ordinary :
      Resource.Event (Sampling.Native.Framed.model t width))
  have zero : ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((recoveryCode spec t).resourcePool path) ≤ 0 := by
    simpa [recoveryCode, ClassicalRoutines.OrderRecovery.Native.eventEnvelope,
      ClassicalRoutines.OrderRecovery.Native.initializationEnvelope,
      ClassicalRoutines.OrderRecovery.Native.visitEnvelope,
      ClassicalRoutines.OrderRecovery.Native.selectionEnvelope,
      ClassicalRoutines.OrderRecovery.Native.candidateEvents,
      ClassicalRoutines.OrderRecovery.Native.validationEvents,
      ClassicalRoutines.OrderRecovery.Native.rejectionEvents,
      ClassicalRoutines.OrderRecovery.Native.acceptanceEvents,
      ClassicalRoutines.Modular.NativePower.eventEnvelope,
      ClassicalRoutines.Modular.NativePower.exponentEnvelope,
      ClassicalRoutines.Modular.NativePower.bitEnvelope,
      ClassicalRoutines.Modular.NativePower.multiplyEnvelope,
      ClassicalRoutines.ConstantWord.envelope,
      ClassicalRoutines.ConstantWord.bitEnvelope,
      ClassicalRoutines.ConstantWord.shiftEvent,
      ClassicalRoutines.ConstantWord.incrementEvent,
      ClassicalRoutines.TerminalDecode.envelope,
      ClassicalRoutines.TerminalDecode.bitEnvelope,
      ClassicalRoutines.TerminalDecode.shiftEvent,
      ClassicalRoutines.TerminalDecode.incrementEvent] using bounded
  exact Nat.eq_zero_of_le_zero zero

/-- Every complete general native run invokes the declared source oracle once. -/
lemma code_modExpCount {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (path : (code spec t).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((code spec t).resourcePool path) = 1 := by
  change ResourcePool.count (model := Sampling.Native.Framed.model t width)
    (.oracle UnitarySource.Coordinate.ordinary)
    (ResourcePool.ofList ((SourceNativeSampling.code t width).eventTrace path.1 ++
      (recoveryCode spec t).eventTrace path.2.2)) = 1
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((SourceNativeSampling.code t width).resourcePool path.1) +
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((recoveryCode spec t).resourcePool path.2.2) = 1
  have sampled :
      ResourcePool.count (model := Sampling.Native.Framed.model t width)
        (.oracle UnitarySource.Coordinate.ordinary)
        ((SourceNativeSampling.code t width).resourcePool path.1) = 1 :=
    Sampling.Native.Framed.code_modExpCount
      (pre width) (pre_quantumWires width) t width path.1
  rw [sampled, recovery_oracleCount_zero, Nat.add_zero]

/-- The public general algorithm uses that same one-query execution. -/
public lemma generalOrderFinding_algorithm_modExpCount {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (path : (algorithm spec t).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((algorithm spec t).run.code.resourcePool path) = 1 :=
  code_modExpCount spec t path

/-- The complete algorithm writes every source phase measurement exactly once. -/
public lemma generalOrderFinding_algorithm_measurementCount {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (path : (algorithm spec t).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.measurement (2 : ℕ+))
      ((algorithm spec t).run.code.resourcePool path) = t := by
  change ResourcePool.count (model := Sampling.Native.Framed.model t width)
    (.measurement (2 : ℕ+)) ((code spec t).resourcePool path) = t
  have bounded := ResourcePool.le_iff_count.mp
    (code_events_le spec t path)
    (.measurement (2 : ℕ+) : Resource.Event (Sampling.Native.Framed.model t width))
  have upper : ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.measurement (2 : ℕ+)) ((code spec t).resourcePool path) ≤ t := by
    simpa [eventBudget, Sampling.Native.eventBudget,
      Sampling.Native.unitaryBudget, ResourcePool.count_add,
      ResourcePool.count_nsmul, ResourcePool.count_singleton,
      ClassicalRoutines.OrderRecovery.Native.eventEnvelope,
      ClassicalRoutines.OrderRecovery.Native.initializationEnvelope,
      ClassicalRoutines.OrderRecovery.Native.visitEnvelope,
      ClassicalRoutines.OrderRecovery.Native.selectionEnvelope,
      ClassicalRoutines.OrderRecovery.Native.candidateEvents,
      ClassicalRoutines.OrderRecovery.Native.validationEvents,
      ClassicalRoutines.OrderRecovery.Native.rejectionEvents,
      ClassicalRoutines.OrderRecovery.Native.acceptanceEvents,
      ClassicalRoutines.Modular.NativePower.eventEnvelope,
      ClassicalRoutines.Modular.NativePower.exponentEnvelope,
      ClassicalRoutines.Modular.NativePower.bitEnvelope,
      ClassicalRoutines.Modular.NativePower.multiplyEnvelope,
      ClassicalRoutines.ConstantWord.envelope,
      ClassicalRoutines.ConstantWord.bitEnvelope,
      ClassicalRoutines.ConstantWord.shiftEvent,
      ClassicalRoutines.ConstantWord.incrementEvent,
      ClassicalRoutines.TerminalDecode.envelope,
      ClassicalRoutines.TerminalDecode.bitEnvelope,
      ClassicalRoutines.TerminalDecode.shiftEvent,
      ClassicalRoutines.TerminalDecode.incrementEvent] using bounded
  have lower : t ≤ ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.measurement (2 : ℕ+)) ((code spec t).resourcePool path) := by
    change t ≤ ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.measurement (2 : ℕ+))
      (ResourcePool.ofList ((SourceNativeSampling.code t width).eventTrace path.1 ++
        (recoveryCode spec t).eventTrace path.2.2))
    rw [ResourcePool.ofList_append, ResourcePool.count_add]
    change t ≤ ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.measurement (2 : ℕ+)) ((SourceNativeSampling.code t width).resourcePool path.1) + _
    rw [SourceNativeSampling.measurementCount t width path.1]
    omega
  omega

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
