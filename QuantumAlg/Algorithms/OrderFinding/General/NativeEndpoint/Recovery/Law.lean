/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Execution
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Correctness

/-!
# Pure recovery value of one actually stored phase word

The finite native recovery's output is defined by reading the measured word
and the original borrowed base from the real sample store. The pure reference
function decodes exactly the same bits and source modulus.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

open QuantumAlg.Execution
open ClassicalRoutines.OrderRecovery.Native

/-- Pure decoded output associated with one stored phase word. -/
def recoveredValue {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width) :
    CShape.Value (.bits t) → CShape.Value (outputShape t)
  | .bits bits => encodeOutput
      (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
        (recoverySpec hinput access) (semanticInput hinput access bits))

/-- The actual finite tail reads the base and sample stored by the same run. -/
theorem recoveryStep_output {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    (store : Store (SourceNativeSampling.post t width))
    (baseValue : store.read (SourceNativeSampling.baseRef t width) =
      encodedBase hinput access) :
    (recoveryStep hinput access store).1.read
      (.storage (resultRef t width).toCStorageRef) =
      recoveredValue hinput access
        (store.read (SourceNativeSampling.sampleRef t width)) := by
  cases measured : store.read (SourceNativeSampling.sampleRef t width) with
  | bits bits =>
      exact recoveryStep_output_of_bits hinput access store bits
        baseValue measured

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
