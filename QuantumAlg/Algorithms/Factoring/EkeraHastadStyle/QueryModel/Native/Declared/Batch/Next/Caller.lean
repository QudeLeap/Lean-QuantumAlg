/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Next.Probability
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Batch.Caller

/-!
# Caller state through a later paid EH batch

The redraw retains every original caller value. The subsequent sixteen paid
same-bank observations also retain it while replacing the source, parameter
and sample cells with one new physical batch.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch

open Execution

noncomputable section

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (N : Nat) (input : Input N)

/-- A complete later physical batch preserves an original caller read jointly
with its new source, parameter and sixteen actual sample outcomes. -/
lemma nextBatch_caller_joint_reference
    {shape : CShape} (observed : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum N) Reference
      ((model N).HiddenState × History))
    (weight : shape.Value → (ParameterShape N).Value →
      (CShape.bits (residueSamplingBits N)).Value → ℂ)
    (outcomes : Fin 16 → Fin (measurementBits N) → Bool)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((nextBatch base noQuantum N).execute (sourceEnvironment input) Reference state)
      (fun entry _ => weight
        (entry.1.read (callerInput base noQuantum N observed))
        (entry.1.read (.storage (parameterRef base noQuantum N).toCStorageRef))
        (entry.1.read (.storage (sourceRef base noQuantum N).toCStorageRef)) *
        terminalIndicator base noQuantum N 16 id outcomes entry.1) left right =
    ExecutionState.referenceFiberSum state
      (fun entry _ => ∑ value : Fin (2 ^ residueSamplingBits N),
        (((2 ^ residueSamplingBits N : Nat) : ℝ)⁻¹ : ℂ) *
          (weight (entry.1.read (callerInput base noQuantum N observed))
            (parameterValue input value)
            (.bits (ShorStyle.Canonical.Sampler.PackedSample.storedBits value)) *
            ∏ index : Fin 16,
              Declared.sourceWeight N input (parameterValue input value) (outcomes index)))
      left right := by
  let oldRead := callerInput base noQuantum N observed
  let sourceRefRead : CInputRef (context base noQuantum N)
      (.bits (residueSamplingBits N)) :=
    .storage (sourceRef base noQuantum N).toCStorageRef
  let jointOld : CInputRef (context base noQuantum N)
      (.product shape (.bits (residueSamplingBits N))) :=
    .product oldRead sourceRefRead
  have measuredFree : ∀ position,
      (Native.cells (storageContext base N) (storage_empty base noQuantum N) N position).key ∉
        jointOld.storageKeys := by
    intro position member
    exact (List.mem_append.mp member).elim
      (caller_measured_separated base noQuantum N observed position)
      (source_measured_separate base noQuantum N position)
  have workingFree :
      (Native.resultRef (storageContext base N) (storage_empty base noQuantum N) N).key ∉
        jointOld.storageKeys := by
    intro member
    exact (List.mem_append.mp member).elim
      (caller_working_separated base noQuantum N observed)
      (source_working_separate base noQuantum N)
  have slotFree : ∀ index,
      (terminalRef base noQuantum N index).key ∉ jointOld.storageKeys := by
    intro index member
    exact (List.mem_append.mp member).elim
      (caller_slot_separated base noQuantum N observed index)
      (fun present => terminal_source_ne base noQuantum N index
        (List.mem_singleton.mp present))
  have separated : RedrawSeparated base noQuantum N oldRead :=
    ⟨caller_source_separated base noQuantum N observed,
      caller_parameter_separated base noQuantum N observed⟩
  have split := Circuit.referenceFiberSum_execute_seq (environment := sourceEnvironment input)
    (redraw base noQuantum N)
    (Circuit.forRange 16 (reusedSample base noQuantum N)) state
    (fun store => weight (store.read oldRead)
      (store.read (.storage (parameterRef base noQuantum N).toCStorageRef))
      (store.read sourceRefRead) *
      terminalIndicator base noQuantum N 16 id outcomes store)
    left right
  have conditional := reusedTerminals_frame_reference base noQuantum N input
    jointOld measuredFree workingFree slotFree
    ((redraw base noQuantum N).execute (sourceEnvironment input) Reference state)
    (fun parameter previous => weight previous.first parameter previous.second)
    outcomes left right
  have drawn := redraw_frame_reference base noQuantum N input oldRead separated state
    (fun previous parameter source => weight previous parameter source *
      ∏ index : Fin 16, Declared.sourceWeight N input parameter (outcomes index))
    left right
  exact split.trans (conditional.trans drawn)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared.Batch
