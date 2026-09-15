/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Context
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Construction

/-!
# Actual general order-finding sampling followed by native recovery

One interpreter executes the original source sample, allocates its final
option cell, and runs finite native continued-fraction recovery on the same
borrowed base and actual measured phase bits. The complete output manifest
retains all live inputs, quantum systems and results. No terminal sampling
wrapper or supplied execution distribution is used.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint

noncomputable section

open QuantumAlg.Execution

/-- Native recovery reads the same actual stored base and sample. -/
def recoveryCode {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) : Circuit (post t width) (post t width) :=
  ClassicalRoutines.OrderRecovery.Native.into (recoverySpec hinput A)
    (baseInput t width) (sampleInput t width) (resultRef t width)

/-- Retain the actual option before running recovery in matched lexical workspace. -/
def recoveryStage {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) :
    Circuit (NativeSampling.post t width) (post t width) :=
  .seq (.retain (NativeSampling.post t width)
    (resultKey t width) (outputShape t) (resultFresh t width)) (recoveryCode hinput A)

/-- The complete actual source sample and finite classical recovery circuit. -/
def code {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) : Circuit (pre width) (post t width) :=
  .seq (NativeSampling.code A) (recoveryStage hinput A)

/-- The complete output reads the actual stored optional candidate. -/
def run {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) :
    AlgorithmRun (pre width) (post t width) (outputShape t) where
  code := code hinput A
  output := Output.all (post t width) (.read (.storage (resultRef t width).toCStorageRef))

theorem run_output_listing {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) :
    (run hinput A).output.listing = (post t width).keys := rfl

theorem run_result {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) (record : (run hinput A).Record) :
    (run hinput A).result record = record.1.read (.storage (resultRef t width).toCStorageRef) := rfl

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint
