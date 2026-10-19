/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Distribution.PMF
import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint.Recovery.Law
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native.Support
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Probability

/-!
# Result law of the actual native source sample and recovery tail

Each supported sampling record retains the original canonical borrowed base.
The genuine finite tail therefore reads the same stored phase word and maps
that record to the pure source recovery value, including its actual path.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

/-- Supported actual records return pure recovery of their own measured bits. -/
lemma recoveredRecord_result {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.Framed.model t width).classicalOracles (pre width) Reference)
    (valid : HasCanonicalBase hinput access input.caller.localState)
    (record : (SourceNativeSampling.run t width).Record)
    (supported : record ∈
      ((SourceNativeSampling.run t width).executionDistribution (Sampling.Native.environment
        access) input).support) :
    (run (modulusSpec hinput access) t).result (recoveredRecord (modulusSpec hinput access) t
      record) =
      recoveredValue hinput access ((SourceNativeSampling.run t width).result record) := by
  change (recoveryStep (modulusSpec hinput access) t record.1).1.read
      (.storage (resultRef t width).toCStorageRef) =
    recoveredValue hinput access (record.1.read (SourceNativeSampling.sampleRef t width))
  exact recoveryStep_output hinput access record.1
    (SourceNativeSampling.supported_base_read hinput access input valid record supported)

/-- Actual complete output is the native sample law followed by genuine recovery. -/
lemma outputDistribution_eq_recovery {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.Framed.model t width).classicalOracles (pre width) Reference)
    (valid : HasCanonicalBase hinput access input.caller.localState) :
    (run (modulusSpec hinput access) t).outputDistribution (Sampling.Native.environment access)
      input =
      ((SourceNativeSampling.run t width).outputDistribution (Sampling.Native.environment access)
        input).map
        (recoveredValue hinput access) := by
  change ((run (modulusSpec hinput access) t).executionDistribution (Sampling.Native.environment
    access) input).map (run (modulusSpec hinput access) t).result =
    (((SourceNativeSampling.run t width).executionDistribution (Sampling.Native.environment
      access) input).map
      (SourceNativeSampling.run t width).result).map (recoveredValue hinput access)
  rw [executionDistribution_eq_map, PMF.map_comp, PMF.map_comp]
  apply PMF.ext
  intro output
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro record
  by_cases supported :
      record ∈ ((SourceNativeSampling.run t width).executionDistribution
        (Sampling.Native.environment access) input).support
  · rw [Function.comp_apply, Function.comp_apply,
      recoveredRecord_result hinput access input valid record supported]
  · have absent := (PMF.apply_eq_zero_iff _ record).2 supported
    simp only [absent, ite_self]

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
