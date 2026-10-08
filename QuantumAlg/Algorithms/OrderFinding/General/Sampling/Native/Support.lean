/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.Sampling.Native.BorrowedReadout
import all QuantumAlg.Core.Execution.Borrowed.Support
import all QuantumAlg.Core.Execution.Probability
import all QuantumAlg.Core.Algorithm.AlgorithmRun

/-!
# Canonical borrowed bases in actual supported sample records

The complete borrowed restoration theorem supplies a supported original
store with the same borrowed value. Initial local support validity then
forces the actual final base read to be canonical. The argument keeps every
external-reference correlation and imposes no independence assumption.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

/-- Every actual supported sample record reads the original canonical borrowed base. -/
theorem supported_base_read {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    {Reference : Register}
    (input : Execution.OracleInput
      (Sampling.Native.Framed.model A).classicalOracles (pre width) Reference)
    (valid : HasCanonicalBase hinput A input.caller.localState)
    (record : (run A).Record)
    (supported : record ∈ ((run A).executionDistribution input).support) :
    record.1.read (baseRef t width) = encodedBase hinput A := by
  have positive := (ExecutionState.mem_support_toPMF_iff
    ((run A).execute Reference input.state) ((run A).execute_normalized input) record).mp supported
  let initial := input.state.mapClassical
    (fun value => (value.1, (value.2, value.1)))
  obtain ⟨original, originalPositive, same⟩ :=
    Circuit.borrowedRestored_supported_initial (code A) Reference initial
      ((run A).execute Reference input.state) (borrowedRestored A initial) record positive
  obtain ⟨sourceEntry, sourceRecord, sourcePositive⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff input.state
      (fun value => (value.1, (value.2, value.1))) original).mp originalPositive
  have originalStore : original.1 = sourceEntry.1 :=
    (congrArg Prod.fst sourceRecord).symm
  have callerPositive :
      0 < ((input.caller.state).block sourceEntry.1).mass :=
    (ExecutionState.mapClassical_block_mass_pos_iff input.state Prod.fst
      sourceEntry.1).2 ⟨sourceEntry, rfl, sourcePositive⟩
  calc
    record.1.read (baseRef t width) = original.1.read (baseSourceRef width) :=
      base_read_of_borrowed_eq A record.1 original.1 same.symm
    _ = sourceEntry.1.read (baseSourceRef width) :=
      congrArg (fun store => store.read (baseSourceRef width)) originalStore
    _ = encodedBase hinput A :=
      canonicalBase_read_of_supported hinput A input.caller valid
        sourceEntry.1 callerPositive

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling
