/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Machine
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Finite.Output
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Initialized.Observation
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Weights.Probability
import all QuantumAlg.Core.Execution.Reference.Probability

/-!
# The genuine initialized Shor machine has the original chronological output law

The real initialized loop clears its own latch, completes each actual recovery
and reset, then pays for its one final pack. Its complete weighted reference
observation and trace-derived output distribution are the original ordered
selection from independent source samples. All parameters remain symbolic.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine

open Execution

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Mathematical chronological result distribution from the original independent source law. -/
def sourceDistribution {N : Nat} (input : Input N) (count : Nat) :
    PMF (CShape.Value (.option (.unsignedWord (modulusBits N)))) :=
  (PMF.independentReplicateVector (sourceOutcomePMF input) count).map
    (fun samples => NativeFactorScan.sourceResults input samples.toList)

/-- Actual initialization supplies the empty latch inside the complete reference equation. -/
theorem code_output_reference (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel input).HiddenState × History))
    (normalized : state.IsNormalized)
    (weight : CShape.Value (.option (.unsignedWord (modulusBits N))) → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum N input count).execute Reference state)
      (fun entry _ => weight (entry.1.read
        (.storage (result base noQuantum N count).toCStorageRef))) left right =
    ExecutionState.referenceFiberSum state
      (fun _ _ => SourceWeights.batch input count
        (fun outcomes => weight (NativeFactorScan.sourceResults input (List.ofFn outcomes))))
      left right := by
  let initial := Initialized.ready base noQuantum N input
  let later := Finite.code (Initialized.bank base noQuantum N) N input
    (Initialized.bank_wires base noQuantum N) count
    (Initialized.cells base noQuantum N) (Initialized.result base noQuantum N)
  have sequence := Circuit.referenceFiberSum_execute_seq initial later state
    (fun store => weight (store.read
      (.storage (result base noQuantum N count).toCStorageRef))) left right
  have repeated := Finite.code_output_reference
    (Initialized.bank base noQuantum N) N input (Initialized.bank_wires base noQuantum N)
    count (Initialized.cells base noQuantum N) (Initialized.result base noQuantum N)
    (Initialized.separated base noQuantum N) (initial.execute Reference state)
    (Initialized.ready_seeded base noQuantum N input state)
    ((initial.execute_mass Reference state).trans normalized) weight left right
  have initialized := Initialized.ready_latch_reference base noQuantum N input state
    (latchedWeight input count weight) left right
  exact sequence.trans (repeated.trans initialized)

/-- Every packed output point preserves all original reference matrix coordinates. -/
theorem code_output_point_reference (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel input).HiddenState × History))
    (normalized : state.IsNormalized)
    (value : CShape.Value (.option (.unsignedWord (modulusBits N))))
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum N input count).execute Reference state)
      (fun entry _ => if entry.1.read
        (.storage (result base noQuantum N count).toCStorageRef) = value then 1 else 0)
      left right =
    ExecutionState.referenceFiberSum state
      (fun _ _ => ((sourceDistribution input count value).toReal : ℂ)) left right := by
  have weights := SourceWeights.batch_indicator input count
    (fun outcomes => NativeFactorScan.sourceResults input (List.ofFn outcomes)) value
  have lists (samples : List.Vector (SourceOutcome N) count) :
      List.ofFn samples.get = samples.toList :=
    (List.Vector.toList_ofFn samples.get).symm.trans
      (congrArg List.Vector.toList (List.Vector.ofFn_get samples))
  have readers :
      (fun samples : List.Vector (SourceOutcome N) count =>
        NativeFactorScan.sourceResults input (List.ofFn samples.get)) =
      (fun samples => NativeFactorScan.sourceResults input samples.toList) := by
    funext samples
    rw [lists]
  rw [readers] at weights
  refine (code_output_reference base noQuantum N input count state normalized
    (fun selected => if selected = value then 1 else 0) left right).trans ?_
  exact congrArg (fun coefficient : ℂ => ExecutionState.referenceFiberSum state
    (fun _ _ => coefficient) left right) weights

/-- Traces of the very same actual execution give the original finite output PMF. -/
theorem code_output_toPMF (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N) (count : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference ((executionModel input).HiddenState × History))
    (normalized : state.IsNormalized) :
    (((code base noQuantum N input count).execute Reference state).toPMF
      (((code base noQuantum N input count).execute_mass Reference state).trans normalized)).map
        (fun entry => entry.1.read
          (.storage (result base noQuantum N count).toCStorageRef)) =
      sourceDistribution input count :=
  ExecutionState.toPMF_map_eq_of_referenceFiberSum state
    ((code base noQuantum N input count).execute Reference state) normalized
    (((code base noQuantum N input count).execute_mass Reference state).trans normalized)
    (fun entry => entry.1.read (.storage (result base noQuantum N count).toCStorageRef))
    (sourceDistribution input count)
    (code_output_point_reference base noQuantum N input count state normalized)

/-- The public run reads its real result with the actual original-store execution history. -/
theorem outputDistribution_eq (base : RuntimeCtx .quantum)
    (noQuantum : base.quantumWires = []) (N : Nat) (input : Input N) (count : Nat)
    {Reference : Register}
    (original : OracleInput (executionModel input).classicalOracles base Reference) :
    (run base noQuantum N input count).outputDistribution original =
      sourceDistribution input count :=
  code_output_toPMF base noQuantum N input count
    (original.state.mapClassical (fun entry => (entry.1, (entry.2, entry.1))))
    ((original.state.mapClassical_mass _).trans original.normalized)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime.Machine
