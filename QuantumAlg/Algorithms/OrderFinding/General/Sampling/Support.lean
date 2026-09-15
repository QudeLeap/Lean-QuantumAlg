/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.BorrowedReadout
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

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeSampling

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

open QuantumAlg.Execution

/-- Every actual supported sample record reads the original canonical borrowed base. -/
theorem supported_base_read {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r) (A : ModExpOracleAccess N x t width)
    {Reference : Register} (input : Execution.Input (pre width) Reference)
    (valid : HasCanonicalBase hinput A input.localState)
    (record : (run A).Record)
    (supported : record ∈ ((run A).executionDistribution input).support) :
    record.1.read (baseRef t width) = encodedBase hinput A := by
  have positive := (ExecutionState.mem_support_toPMF_iff
    ((run A).execute Reference input.state) ((run A).execute_normalized input) record).mp supported
  let initial := input.state.mapClassical (fun store => (store, store))
  obtain ⟨original, originalPositive, same⟩ :=
    Circuit.borrowedRestored_supported_initial (code A) Reference initial
      ((run A).execute Reference input.state) (borrowedRestored A initial) record positive
  have decisionEquality : initial =
      @ExecutionState.mapClassical (Store (pre width)) (Store (pre width) × Store (pre width))
        _ _ (Register.prod (pre width).register Reference) (Classical.decEq _) input.state
        (fun store => (store, store)) :=
    congrArg (fun decision : DecidableEq (Store (pre width) × Store (pre width)) =>
      @ExecutionState.mapClassical (Store (pre width)) (Store (pre width) × Store (pre width))
        _ _ (Register.prod (pre width).register Reference) decision input.state
        (fun store => (store, store))) (Subsingleton.elim _ _)
  have sourceMappedPositive :
      0 < ((@ExecutionState.mapClassical (Store (pre width))
        (Store (pre width) × Store (pre width)) _ _
        (Register.prod (pre width).register Reference) (Classical.decEq _) input.state
        (fun store => (store, store))).block original).mass :=
    (congrArg (fun actual => 0 < (actual.block original).mass) decisionEquality).mp originalPositive
  obtain ⟨sourceStore, sourceRecord, sourcePositive⟩ :=
    (ExecutionState.mapClassical_block_mass_pos_iff input.state
      (fun store => (store, store)) original).mp sourceMappedPositive
  have originalStore : original.1 = sourceStore := (congrArg Prod.fst sourceRecord).symm
  calc
    record.1.read (baseRef t width) = original.1.read (baseSourceRef width) :=
      base_read_of_borrowed_eq A record.1 original.1 same.symm
    _ = sourceStore.read (baseSourceRef width) :=
      congrArg (fun store => store.read (baseSourceRef width)) originalStore
    _ = encodedBase hinput A :=
      canonicalBase_read_of_supported hinput A input valid sourceStore sourcePositive

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeSampling
