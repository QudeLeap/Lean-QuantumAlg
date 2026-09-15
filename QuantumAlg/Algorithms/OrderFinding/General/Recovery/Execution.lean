/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Execution
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Correctness
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Execution
import all QuantumAlg.Core.Execution.Retained.Composition

/-!
# Actual native recovery records after the source sample

The sole interpreter retains the result cell and executes the existing native
recovery program. The same final store and actual path determine the record
map. Reading that store gives the original source recovery result for the
actual measured bits whenever its original borrowed base has the source value.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution
open ClassicalRoutines.OrderRecovery.Native

/-- The actual retained-result allocation and complete scoped recovery record. -/
def recoveryStep {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) (store : Store (NativeSampling.post t width)) :
    Store (post t width) × (recoveryStage hinput A).Path :=
  let actual := intoStep (recoverySpec hinput A) (baseInput t width) (sampleInput t width)
    (resultRef t width)
    (store.pushRetained (resultKey t width) (outputShape t) (resultFresh t width))
  (actual.1, ((), actual.2))

/-- The actual classical tail maps the same full reference blocks and finite histories. -/
theorem recoveryStage_execute {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (NativeSampling.post t width) Reference History) :
    (recoveryStage hinput A).execute Reference state =
      state.mapClassical (fun entry =>
        ((recoveryStep hinput A entry.1).1, (entry.2, (recoveryStep hinput A entry.1).2))) := by
  refine (Circuit.execute_retain_seq_mapClassical (NativeSampling.post t width)
    (resultKey t width) (outputShape t) (resultFresh t width) (recoveryCode hinput A)
    (intoStep (recoverySpec hinput A) (baseInput t width) (sampleInput t width) (resultRef t width))
    (nativeRecovery_into_execute (recoverySpec hinput A) (baseInput t width)
      (sampleInput t width) (resultRef t width)) Reference state).trans ?_
  exact mapDecision _ _ state (fun entry =>
    ((recoveryStep hinput A entry.1).1, (entry.2, (recoveryStep hinput A entry.1).2)))

/-- The mathematical output encoding attached to an actually measured source outcome. -/
def recoveredValue {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) : CShape.Value (.bits t) → CShape.Value (outputShape t)
  | .bits bits => encodeOutput
      (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
        (recoverySpec hinput A) (semanticInput hinput A bits))

/-- The actual final result is the source recovery of those very same measured bits. -/
theorem recoveryStep_output_of_bits {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (store : Store (NativeSampling.post t width)) (bits : Outcome t)
    (baseValue : store.read (NativeSampling.baseRef t width) = encodedBase hinput A)
    (measured : store.read (NativeSampling.sampleRef t width) = .bits bits) :
    (recoveryStep hinput A store).1.read (.storage (resultRef t width).toCStorageRef) =
      recoveredValue hinput A (.bits bits) := by
  apply nativeRecovery_into_result (recoverySpec hinput A) (semanticInput hinput A bits)
  · exact (baseInput_read t width store).trans baseValue
  · exact (sampleInput_read t width store).trans measured

/-- The actual tail result is recovered from its real sample read on every canonical-base store. -/
theorem recoveryStep_output {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    (store : Store (NativeSampling.post t width))
    (baseValue : store.read (NativeSampling.baseRef t width) = encodedBase hinput A) :
    (recoveryStep hinput A store).1.read (.storage (resultRef t width).toCStorageRef) =
      recoveredValue hinput A (store.read (NativeSampling.sampleRef t width)) := by
  cases measured : store.read (NativeSampling.sampleRef t width) with
  | bits bits => exact recoveryStep_output_of_bits hinput A store bits baseValue measured

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint
