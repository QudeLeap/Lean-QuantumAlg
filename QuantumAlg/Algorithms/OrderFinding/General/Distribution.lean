/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Recovery.Execution
import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Support
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Execution.MappedTail
import all QuantumAlg.Core.Measure.Distribution

/-!
# The actual general order-finding output distribution

The genuine recovery tail maps the very same source-sampling records. Its
source-result equation applies on actual support because joint borrowed
restoration retains the canonical input base there. Reading complete Output
therefore gives the original Born distribution mapped by the original finite
recovery function, for arbitrary external-reference extensions.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

/-- Append the real recovery store and path to the actual sampling record. -/
def recoveredRecord {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) (record : (NativeSampling.run A).Record) :
    (run hinput A).Record :=
  ((recoveryStep hinput A record.1).1,
    (record.2.1, (record.2.2, (recoveryStep hinput A record.1).2)))

/-- The complete execution maps the same actual sampling blocks and all their correlations. -/
theorem execute_eq_map {N x r t width : Nat} (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t width) (Reference : Register)
    (state : ExecutionState (Store (pre width)) (Register.prod (pre width).register Reference)) :
    (run hinput A).execute Reference state =
      ((NativeSampling.run A).execute Reference state).mapClassical (recoveredRecord hinput A) := by
  refine (Circuit.execute_seq_retained_mapClassical_tail
    (resultKey t width) (outputShape t) (resultFresh t width)
    (NativeSampling.code A) (recoveryStage hinput A) (recoveryStep hinput A)
    (recoveryStage_execute hinput A) Reference
    (state.mapClassical (fun store => (store, store)))).trans ?_
  exact congrArg (fun decision : DecidableEq (run hinput A).Record =>
    @ExecutionState.mapClassical (NativeSampling.run A).Record (run hinput A).Record _ _
      (Register.prod (NativeSampling.post t width).register Reference) decision
      ((NativeSampling.run A).execute Reference state) (recoveredRecord hinput A))
    (Subsingleton.elim _ _)

/-- The actual full-record probability distribution follows its genuine recovery map. -/
theorem executionDistribution_eq_map {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    {Reference : Register} (input : Execution.Input (pre width) Reference) :
    (run hinput A).executionDistribution input =
      ((NativeSampling.run A).executionDistribution input).map (recoveredRecord hinput A) := by
  apply PMF.ext
  intro record
  change ENNReal.ofReal ((((run hinput A).execute Reference input.state).block record).mass) = _
  rw [execute_eq_map]
  exact congrArg (fun distribution : PMF (run hinput A).Record => distribution record)
    (ExecutionState.toPMF_mapClassical ((NativeSampling.run A).execute Reference input.state)
      ((NativeSampling.run A).execute_normalized input) (recoveredRecord hinput A))

/-- Every supported actual record returns the original recovery of its own actual sample read. -/
theorem recoveredRecord_result {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    {Reference : Register} (input : Execution.Input (pre width) Reference)
    (valid : HasCanonicalBase hinput A input.localState)
    (record : (NativeSampling.run A).Record)
    (supported : record ∈ ((NativeSampling.run A).executionDistribution input).support) :
    (run hinput A).result (recoveredRecord hinput A record) =
      recoveredValue hinput A ((NativeSampling.run A).result record) :=
  recoveryStep_output hinput A record.1
    (NativeSampling.supported_base_read hinput A input valid record supported)

/-- Complete Output is the real sample distribution followed by its actual recovery decoding. -/
theorem outputDistribution_eq_recovery {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    {Reference : Register} (input : Execution.Input (pre width) Reference)
    (valid : HasCanonicalBase hinput A input.localState) :
    (run hinput A).outputDistribution input =
      ((NativeSampling.run A).outputDistribution input).map (recoveredValue hinput A) := by
  change ((run hinput A).executionDistribution input).map (run hinput A).result =
    (((NativeSampling.run A).executionDistribution input).map (NativeSampling.run A).result).map
      (recoveredValue hinput A)
  rw [executionDistribution_eq_map, PMF.map_comp, PMF.map_comp]
  apply PMF.ext
  intro output
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro record
  by_cases supported : record ∈ ((NativeSampling.run A).executionDistribution input).support
  · rw [Function.comp_apply, Function.comp_apply,
      recoveredRecord_result hinput A input valid record supported]
  · have absent := (PMF.apply_eq_zero_iff _ record).2 supported
    simp only [absent, ite_self]

/-- The actual full native run has the original source Born-and-recovery law. -/
theorem outputDistribution_eq {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    {Reference : Register} (input : Execution.Input (pre width) Reference)
    (valid : HasCanonicalBase hinput A input.localState) :
    (run hinput A).outputDistribution input =
      ((measurement t width).outcomePMF (BornBridge.evolvedState A)).map (fun outcome =>
        ClassicalRoutines.OrderRecovery.Native.encodeOutput
          (ClassicalAlgorithms.OrderRecovery.recoverUnitOrder
            (recoverySpec hinput A) (semanticInput hinput A outcome))) := by
  rw [outputDistribution_eq_recovery hinput A input valid, NativeSampling.distribution,
    PMF.map_comp]
  rfl

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeEndpoint
