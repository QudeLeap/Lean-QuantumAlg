/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint
import all QuantumAlg.Algorithms.OrderFinding.General.Input
import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Specification
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Correctness
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Execution
import all QuantumAlg.Core.Execution.Store

/-!
# Native recovery of the actually stored source sample

The finite recovery stage reads the original borrowed residue and packed
phase word through structural references. Its final option equals the pure
fixed-width recovery result for those exact stored values.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

open QuantumAlg.Execution
open ClassicalRoutines.OrderRecovery.Native

/-- Retaining the result cell does not change the original borrowed-base read. -/
theorem baseInput_read (t width : Nat)
    (store : Store (SourceNativeSampling.post t width)) :
    (store.pushRetained (resultKey t width) (outputShape t)
      (resultFresh t width)).read (baseInput t width) =
      store.read (SourceNativeSampling.baseRef t width) :=
  Store.read_pushRetained_underRetained store _ _ _ _

/-- Retaining the option also preserves the actual measured phase-word read. -/
theorem sampleInput_read (t width : Nat)
    (store : Store (SourceNativeSampling.post t width)) :
    (store.pushRetained (resultKey t width) (outputShape t)
      (resultFresh t width)).read (sampleInput t width) =
      store.read (SourceNativeSampling.sampleRef t width) :=
  Store.read_pushRetained_underRetained store _ _ _ _

/-- One concrete finite recovery step starts from the actual sample store. -/
def recoveryStep {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    (store : Store (SourceNativeSampling.post t width)) :
    Store (post t width) × (recoveryStage hinput access).Path :=
  let actual := intoStep (model := Sampling.Native.Framed.model access)
    (recoverySpec hinput access) (baseInput t width) (sampleInput t width)
    (resultRef t width)
    (store.pushRetained (resultKey t width) (outputShape t) (resultFresh t width))
  (actual.1, ((), actual.2))

/-- Correct canonical-base and measured-bit cells yield the pure recovery option. -/
theorem recoveryStep_output_of_bits {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    (store : Store (SourceNativeSampling.post t width))
    (bits : ClassicalAlgorithms.OrderRecovery.TerminalBits t)
    (baseValue : store.read (SourceNativeSampling.baseRef t width) =
      encodedBase hinput access)
    (measured : store.read (SourceNativeSampling.sampleRef t width) = .bits bits) :
    (recoveryStep hinput access store).1.read
      (.storage (resultRef t width).toCStorageRef) =
      encodeOutput (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
        (recoverySpec hinput access) (semanticInput hinput access bits)) := by
  change (intoStep (model := Sampling.Native.Framed.model access)
    (recoverySpec hinput access) (baseInput t width) (sampleInput t width)
    (resultRef t width)
    (store.pushRetained (resultKey t width) (outputShape t)
      (resultFresh t width))).1.read (cellRead (resultRef t width)) = _
  exact nativeRecovery_into_result
    (model := Sampling.Native.Framed.model access)
    (recoverySpec hinput access) (semanticInput hinput access bits)
    (baseInput t width) (sampleInput t width) (resultRef t width)
    (store.pushRetained (resultKey t width) (outputShape t) (resultFresh t width))
    ((baseInput_read t width store).trans baseValue)
    ((sampleInput_read t width store).trans measured)

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
