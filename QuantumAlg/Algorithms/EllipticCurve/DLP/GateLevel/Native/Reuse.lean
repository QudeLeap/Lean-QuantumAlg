/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.GateLevel.Native.Probability
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Sequence.Observation

/-!
# Original Born sampling after actual allocation and paid bank reuse

The actual preparation supplies the first seed. Each later round establishes
that same seed by measuring and correcting every live wire, while preserving
all incoming structural operands jointly with the external reference. Thus
the original conditional Born law holds on arbitrary incoming states without
requiring callers to promise a clean bank or initialized measurement cells.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
namespace GateLevelAttempt.Native

open Execution

noncomputable section

variable {p : Nat} {E : PrimeFieldShortWeierstrass p}
  (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (I : ECDLPInstance E)

private theorem resetCell_key (wire : Fin (context base noQuantum I).systemCount) :
    (resetCell base noQuantum I wire).key =
      (cells base noQuantum I ⟨0, sampleWidth_pos I⟩).key :=
  FiniteReadout.transported_key
    (nativeECDLP_context_qubits I (nativeECDLP_context_wires base noQuantum I) wire)
    (cells base noQuantum I ⟨0, sampleWidth_pos I⟩)

/-- Actual reset preserves each incoming structural operand's full reference weight. -/
theorem nativeECDLP_reset_reference {shape : CShape} (input : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum I) Reference History) (weight : shape.Value → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((reset base noQuantum I).execute Reference state)
        (fun entry _ => weight (entry.1.read (liftInput base noQuantum I input))) left right =
      ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read (liftInput base noQuantum I input))) left right := by
  have unchanged : ∀ (wire : Fin (context base noQuantum I).systemCount)
      (store : Store (context base noQuantum I)) result,
      weight ((store.write (resetCell base noQuantum I wire) result).read
        (liftInput base noQuantum I input)) =
      weight (store.read (liftInput base noQuantum I input)) := by
    intro wire store result
    apply congrArg weight
    apply Store.read_write_of_not_mem_storageKeys
    rw [resetCell_key]
    exact MeasurementCells.reference_not_mem_liftInput 2 _ (sampleWidth I) _
  exact QuditShift.resetToBasis_weighted_reference (resetCell base noQuantum I)
    (resetLabel base noQuantum I) state
    (fun store => weight (store.read (liftInput base noQuantum I input))) unchanged left right

/-- The actual initial preparation and finite allocations discharge the original seed premise. -/
theorem nativeECDLP_first_outcome_reference
    (B : OrderExpansion (problem I).order) (A : Access I)
    {shape : CShape} (input : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference History) (weight : shape.Value → ℂ)
    (outcome : Fin (sampleWidth I) → Bool) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum ((run base noQuantum I B A).code.execute Reference state)
        (fun entry _ => weight (entry.1.read (liftInput base noQuantum I input)) *
          if observedOutcome I (entry.1.read (sampleInput base noQuantum I)) = outcome
          then 1 else 0) left right =
      ((outcomePMF I B A outcome).toReal : ℂ) * ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read input)) left right := by
  classical
  have first := Circuit.referenceFiberSum_execute_seq (allocate base noQuantum I)
    (sample base noQuantum I B A) state
    (fun store => weight (store.read (liftInput base noQuantum I input)) *
      if observedOutcome I (store.read (sampleInput base noQuantum I)) = outcome
      then (1 : ℂ) else 0) left right
  have born := nativeECDLP_sample_outcome_reference base noQuantum I B A input
    ((allocate base noQuantum I).execute Reference state)
    (nativeECDLP_allocate_seeded base noQuantum I state) weight outcome left right
  exact first.trans (born.trans (congrArg
    (fun coefficient : ℂ => ((outcomePMF I B A outcome).toReal : ℂ) * coefficient)
    (nativeECDLP_allocate_reference base noQuantum I input state weight left right)))

/-- Every later actual round has the same original law after its own paid reset. -/
theorem nativeECDLP_reusedSample_outcome_reference
    (B : OrderExpansion (problem I).order) (A : Access I)
    {shape : CShape} (input : CInputRef base shape)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context base noQuantum I) Reference History) (weight : shape.Value → ℂ)
    (outcome : Fin (sampleWidth I) → Bool) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
        ((reusedSample base noQuantum I B A).execute Reference state)
        (fun entry _ => weight (entry.1.read (liftInput base noQuantum I input)) *
          if observedOutcome I (entry.1.read (sampleInput base noQuantum I)) = outcome
          then 1 else 0) left right =
      ((outcomePMF I B A outcome).toReal : ℂ) * ExecutionState.referenceFiberSum state
        (fun entry _ => weight (entry.1.read (liftInput base noQuantum I input))) left right := by
  classical
  have first := Circuit.referenceFiberSum_execute_seq (reset base noQuantum I)
    (sample base noQuantum I B A) state
    (fun store => weight (store.read (liftInput base noQuantum I input)) *
      if observedOutcome I (store.read (sampleInput base noQuantum I)) = outcome
      then (1 : ℂ) else 0) left right
  have born := nativeECDLP_sample_outcome_reference base noQuantum I B A input
    ((reset base noQuantum I).execute Reference state)
    (nativeECDLP_reset_seeded base noQuantum I state) weight outcome left right
  exact first.trans (born.trans (congrArg
    (fun coefficient : ℂ => ((outcomePMF I B A outcome).toReal : ℂ) * coefficient)
    (nativeECDLP_reset_reference base noQuantum I input state weight left right)))

end

end GateLevelAttempt.Native
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Canonical
