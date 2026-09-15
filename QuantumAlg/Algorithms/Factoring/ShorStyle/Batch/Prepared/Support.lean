/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Context
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Batch.Prepared.Probability
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Readout
import all QuantumAlg.Core.Algorithm.AlgorithmRun
import all QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Measure.Distribution

/-!
# Actual supported Shor tuples have the original source meaning

The already proved Born law of the actual sampling batch identifies every
positive-probability stored tuple vector with its original source transcript.
This supplies the parameter and phase agreement needed by native recovery
internally. No independent source distribution or consistency certificate is
part of the executable input, including for correlated reference extensions.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The complete actual sampling output has the source law in its genuine retained encoding. -/
theorem sampled_outputDistribution {N : Nat} (source : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input pre Reference) :
    (NativePreparedBatch.run pre pre_quantumWires N count).outputDistribution input =
      (PMF.independentReplicateVector (sourceOutcomePMF source) count).map
        (NativeSourceReadout.encoding source) :=
  NativePreparedBatch.code_outputPMF pre pre_quantumWires source count
    (input.state.mapClassical (fun store => (store, store)))
    ((input.state.mapClassical_mass _).trans input.normalized)

/-- Each supported actual record reads a complete tuple vector encoded by the original source. -/
theorem sampled_supported_source {N : Nat} (source : Input N) (count : Nat)
    {Reference : Register} (input : Execution.Input pre Reference)
    (record : (NativePreparedBatch.run pre pre_quantumWires N count).Record)
    (supported : record ∈
      ((NativePreparedBatch.run pre pre_quantumWires N count).executionDistribution
        input).support) :
    ∃ samples : List.Vector (SourceOutcome N) count,
      record.1.read (NativeBatch.readout (NativeBank.context pre pre_quantumWires N) N count) =
        NativeSourceReadout.encoding source samples := by
  have actual : (NativePreparedBatch.run pre pre_quantumWires N count).result record ∈
      ((NativePreparedBatch.run pre pre_quantumWires N count).outputDistribution input).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨record, supported, rfl⟩
  rw [sampled_outputDistribution source count input] at actual
  obtain ⟨samples, _positive, same⟩ := (PMF.mem_support_map_iff _ _ _).mp actual
  exact ⟨samples, same.symm⟩

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeEndpoint
