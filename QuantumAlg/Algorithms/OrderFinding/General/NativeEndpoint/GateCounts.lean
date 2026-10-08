/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Counts
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Counts
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native.Counts

/-!
# Native gate coordinates of complete general order finding

The declared modular-exponentiation query remains sealed. Its peripheral
phase gates expand into the selected native gate model, while finite classical
recovery adds no quantum gates to the same complete execution path.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

private theorem recovery_gateCount_zero {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    (coordinate : AlgorithmGate.Coordinate)
    (path : (recoveryCode hinput access).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate coordinate) ((recoveryCode hinput access).resourcePool path) = 0 := by
  have bounded := ResourcePool.le_iff_count.mp
    (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_pool_le
      (model := Sampling.Native.Framed.model access)
      (recoverySpec hinput access) (baseInput t width) (sampleInput t width)
      (resultRef t width) path) (.gate coordinate :
        Resource.Event (Sampling.Native.Framed.model access))
  have zero : ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate coordinate) ((recoveryCode hinput access).resourcePool path) ≤ 0 := by
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

private theorem code_gateCount {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    (coordinate : AlgorithmGate.Coordinate)
    (path : (code hinput access).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate coordinate) ((code hinput access).resourcePool path) =
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate coordinate) ((SourceNativeSampling.code access).resourcePool path.1) := by
  change ResourcePool.count (model := Sampling.Native.Framed.model access)
    (.gate coordinate)
    (ResourcePool.ofList ((SourceNativeSampling.code access).eventTrace path.1 ++
      (recoveryCode hinput access).eventTrace path.2.2)) = _
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate coordinate) ((SourceNativeSampling.code access).resourcePool path.1) +
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate coordinate) ((recoveryCode hinput access).resourcePool path.2.2) = _
  rw [recovery_gateCount_zero hinput access coordinate, Nat.add_zero]

/-- The complete execution has the native single-qubit expansion of the source sample. -/
public theorem generalOrderFinding_algorithm_singleQubitCount {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    (path : (algorithm hinput access).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate .singleQubit) ((algorithm hinput access).run.code.resourcePool path) =
      2 * t + 3 * t.choose 2 := by
  change ResourcePool.count (model := Sampling.Native.Framed.model access)
    (.gate .singleQubit) ((code hinput access).resourcePool path) = _
  rw [code_gateCount hinput access .singleQubit path]
  exact SourceNativeSampling.singleQubitCount access path.1

/-- Controlled phases and SWAPs retain their physical CNOT expansion. -/
public theorem generalOrderFinding_algorithm_cnotCount {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    (path : (algorithm hinput access).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate .cnot) ((algorithm hinput access).run.code.resourcePool path) =
      2 * t.choose 2 + 3 * (t / 2) := by
  change ResourcePool.count (model := Sampling.Native.Framed.model access)
    (.gate .cnot) ((code hinput access).resourcePool path) = _
  rw [code_gateCount hinput access .cnot path]
  exact SourceNativeSampling.cnotCount access path.1

/-- The only possible Toffoli work is internal to the sealed source query. -/
public theorem generalOrderFinding_algorithm_toffoliCount {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    (path : (algorithm hinput access).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.gate .toffoli) ((algorithm hinput access).run.code.resourcePool path) = 0 := by
  change ResourcePool.count (model := Sampling.Native.Framed.model access)
    (.gate .toffoli) ((code hinput access).resourcePool path) = _
  rw [code_gateCount hinput access .toffoli path]
  exact SourceNativeSampling.toffoliCount access path.1

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
