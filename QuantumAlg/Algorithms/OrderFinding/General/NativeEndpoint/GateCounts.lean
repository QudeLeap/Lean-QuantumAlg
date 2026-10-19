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

private lemma recovery_gateCount_zero {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (coordinate : AlgorithmGate.Coordinate)
    (path : (recoveryCode spec t).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate coordinate) ((recoveryCode spec t).resourcePool path) = 0 := by
  have bounded := ResourcePool.le_iff_count.mp
    (ClassicalRoutines.OrderRecovery.Native.nativeRecovery_into_pool_le
      (model := Sampling.Native.Framed.model t width)
      (⟨spec⟩ : ClassicalAlgorithms.OrderRecovery.Spec width t) (baseInput t width) (sampleInput t
        width)
      (resultRef t width) path) (.gate coordinate :
        Resource.Event (Sampling.Native.Framed.model t width))
  have zero : ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate coordinate) ((recoveryCode spec t).resourcePool path) ≤ 0 := by
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

private lemma code_gateCount {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (coordinate : AlgorithmGate.Coordinate)
    (path : (code spec t).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate coordinate) ((code spec t).resourcePool path) =
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate coordinate) ((SourceNativeSampling.code t width).resourcePool path.1) := by
  change ResourcePool.count (model := Sampling.Native.Framed.model t width)
    (.gate coordinate)
    (ResourcePool.ofList ((SourceNativeSampling.code t width).eventTrace path.1 ++
      (recoveryCode spec t).eventTrace path.2.2)) = _
  rw [ResourcePool.ofList_append, ResourcePool.count_add]
  change ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate coordinate) ((SourceNativeSampling.code t width).resourcePool path.1) +
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate coordinate) ((recoveryCode spec t).resourcePool path.2.2) = _
  rw [recovery_gateCount_zero spec t coordinate, Nat.add_zero]

/-- The complete execution has the native single-qubit expansion of the source sample. -/
public lemma generalOrderFinding_algorithm_singleQubitCount {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (path : (algorithm spec t).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate .singleQubit) ((algorithm spec t).run.code.resourcePool path) =
      2 * t + 3 * t.choose 2 := by
  change ResourcePool.count (model := Sampling.Native.Framed.model t width)
    (.gate .singleQubit) ((code spec t).resourcePool path) = _
  rw [code_gateCount spec t .singleQubit path]
  exact SourceNativeSampling.singleQubitCount t width path.1

/-- Controlled phases and SWAPs retain their physical CNOT expansion. -/
public lemma generalOrderFinding_algorithm_cnotCount {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (path : (algorithm spec t).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate .cnot) ((algorithm spec t).run.code.resourcePool path) =
      2 * t.choose 2 + 3 * (t / 2) := by
  change ResourcePool.count (model := Sampling.Native.Framed.model t width)
    (.gate .cnot) ((code spec t).resourcePool path) = _
  rw [code_gateCount spec t .cnot path]
  exact SourceNativeSampling.cnotCount t width path.1

/-- The only possible Toffoli work is internal to the sealed source query. -/
public lemma generalOrderFinding_algorithm_toffoliCount {width : Nat}
    (spec : ClassicalAlgorithms.Modular.ModulusSpec width) (t : Nat)
    (path : (algorithm spec t).run.code.Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.gate .toffoli) ((algorithm spec t).run.code.resourcePool path) = 0 := by
  change ResourcePool.count (model := Sampling.Native.Framed.model t width)
    (.gate .toffoli) ((code spec t).resourcePool path) = _
  rw [code_gateCount spec t .toffoli path]
  exact SourceNativeSampling.toffoliCount t width path.1

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
