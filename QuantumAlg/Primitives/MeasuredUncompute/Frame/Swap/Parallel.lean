/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Swap.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Placement

/-!
# The actual parallel three-CNOT word exchange

Every selected pair executes its original three native CNOTs in sequence.
Disjoint pairs execute in parallel; physical inclusion retains the complete
original frame. The complete operator equals the original serial gate word.
-/

namespace QuantumAlg.MeasuredUncompute.FrameSwapParallel

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open ProductPlacement FramePorts FrameSwapLayout
open QuantumLayout.Embedding (compose embedding_lift_compose embedding_lift_mul)

private def identityPlacement {count : Nat} (physical : QuantumLayout count) :
    QuantumLayout.Embedding physical physical where
  position := Function.Embedding.refl _
  wire_eq _ := rfl

private def reversed (width : Nat) (index : Fin width) :
    QuantumLayout.Embedding (reverseApplication width index).occurrence.placement.layout
      (application width index).occurrence.placement.layout where
  position := (Fin.revPerm (n := 2)).toEmbedding
  wire_eq position := by fin_cases position <;> rfl

private def forward (width : Nat) (index : Fin width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (application width index).occurrence.placement.layout :=
  .native { occurrence := (application width index).occurrence
            embedding := identityPlacement (application width index).occurrence.placement.layout }

private def backward (width : Nat) (index : Fin width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (application width index).occurrence.placement.layout :=
  .native { occurrence := (reverseApplication width index).occurrence
            embedding := reversed width index }

private lemma forward_lift (width : Nat) (index : Fin width) :
    (application width index).embedding.liftOperator ((forward width index).matrix environment) =
      (application width index).operator := by
  change (application width index).embedding.liftOperator
      ((identityPlacement (application width index).occurrence.placement.layout).liftOperator
        (application width index).occurrence.operator) = _
  rw [embedding_lift_compose]
  rfl

private lemma backward_lift (width : Nat) (index : Fin width) :
    (application width index).embedding.liftOperator ((backward width index).matrix environment) =
      (reverseApplication width index).operator := by
  change (application width index).embedding.liftOperator
      ((reversed width index).liftOperator (reverseApplication width index).occurrence.operator) = _
  rw [embedding_lift_compose]
  have placement : compose (reversed width index) (application width index).embedding =
      (reverseApplication width index).embedding := by
    apply QuantumLayout.Embedding.embedding_ext
    intro position
    fin_cases position <;> rfl
  rw [placement]
  rfl

def localSwap (width : Nat) (index : Fin width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (application width index).occurrence.placement.layout :=
  (forward width index).seq ((backward width index).seq (forward width index))

lemma localSwap_lift_matrix (width : Nat) (index : Fin width) :
    (application width index).embedding.liftOperator ((localSwap width index).matrix environment) =
      ((EncodedBit.swapProgram (QubitLayout.canonical _) .empty
        ((accumulator width).bit index) ((numerator width).bit index)
        (accumulator_numerator_ne width index index)).matrix environment) := by
  rw [localSwap, UnitaryCircuit.seq_matrix, UnitaryCircuit.seq_matrix,
    embedding_lift_mul, embedding_lift_mul, forward_lift, backward_lift]
  simp only [EncodedBit.swapProgram, EncodedBit.swapGates, EncodedBit.GateSpec.programList,
    UnitaryCircuit.seq_matrix, UnitaryCircuit.identity_matrix, one_mul]
  rfl

def word (width : Nat) : (count : Nat) → (bounded : count ≤ width) →
    UnitaryCircuit AlgorithmGate.model .empty (subsystem width count bounded)
  | 0, _ => .identity AlgorithmGate.model .empty _
  | count + 1, bounded =>
      .parallel (word width count (Nat.le_of_succ_le bounded))
        (localSwap width ⟨count, Nat.lt_of_succ_le bounded⟩)
        (earlier width count bounded) (next width count bounded) (disjoint width count bounded)

lemma word_eventTrace (width count : Nat) (bounded : count ≤ width) :
    (word width count bounded).eventTrace =
      List.replicate (3 * count)
        (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .cnot) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change (word width count _).eventTrace ++ [.gate .cnot, .gate .cnot, .gate .cnot] = _
      rw [ih, show 3 * (count + 1) = 3 * count + 3 by omega, List.replicate_add]
      rfl

lemma word_depth (width count : Nat) (bounded : count ≤ width) :
    (word width count bounded).evaluatedEventDepth (fun _ => 1) =
      if count = 0 then 0 else 3 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [word, UnitaryCircuit.evaluatedEventDepth_parallel, ih]
      change max (if count = 0 then 0 else 3) 3 = _
      by_cases empty : count = 0 <;> simp [empty]

def swapPrefix (width count : Nat) (bounded : count ≤ width) :
    UnitaryCircuit AlgorithmGate.model .empty (layout width) :=
  (word width count bounded).embed (complete width count bounded)

lemma prefix_zero_matrix (width : Nat) (bounded : 0 ≤ width) :
    ((swapPrefix width 0 bounded).matrix environment) = 1 := by
  rw [swapPrefix, UnitaryCircuit.embed_matrix, word, UnitaryCircuit.identity_matrix,
    QuantumLayout.Embedding.embedding_liftOperator_one]

lemma prefix_succ_matrix (width count : Nat) (bounded : count + 1 ≤ width) :
    ((swapPrefix width (count + 1) bounded).matrix environment) =
      ((EncodedBit.swapProgram (QubitLayout.canonical _) .empty
        ((accumulator width).bit ⟨count, Nat.lt_of_succ_le bounded⟩)
        ((numerator width).bit ⟨count, Nat.lt_of_succ_le bounded⟩)
        (accumulator_numerator_ne width ⟨count, Nat.lt_of_succ_le bounded⟩
          ⟨count, Nat.lt_of_succ_le bounded⟩)).matrix environment) *
      ((swapPrefix width count (Nat.le_of_succ_le bounded)).matrix environment) := by
  rw [swapPrefix, UnitaryCircuit.embed_matrix, word, UnitaryCircuit.parallel_matrix_raw,
    embedding_lift_mul, embedding_lift_compose, embedding_lift_compose,
    next_complete, earlier_complete,
    localSwap_lift_matrix]
  rfl

private def gates (width : Nat) (indices : List (Fin width)) :=
  indices.flatMap fun index => EncodedBit.swapGates
    ((accumulator width).bit index) ((numerator width).bit index)
    (accumulator_numerator_ne width index index)

private lemma list_append_matrix (width : Nat)
    (first second : List (EncodedBit.GateSpec (frameEncoding width))) :
    ((EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty (first ++ second)).matrix
      environment) =
      ((EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty second).matrix environment)
        *
      ((EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty first).matrix environment)
        := by
  induction first with
  | nil => simp only [List.nil_append, EncodedBit.GateSpec.programList,
      UnitaryCircuit.identity_matrix, mul_one]
  | cons gate rest ih =>
      simp only [List.cons_append, EncodedBit.GateSpec.programList, UnitaryCircuit.seq_matrix]
      rw [ih, mul_assoc]

lemma prefix_matrix (width count : Nat) (bounded : count ≤ width) :
    ((swapPrefix width count bounded).matrix environment) =
      ((EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty
        (gates width ((List.ofFn fun index : Fin width => index).take count))).matrix environment)
          := by
  induction count with
  | zero => exact prefix_zero_matrix width bounded
  | succ count ih =>
      have within : count < (List.ofFn fun index : Fin width => index).length := by
        simpa only [List.length_ofFn] using Nat.lt_of_succ_le bounded
      rw [prefix_succ_matrix, ih, ← List.take_concat_get' _ count within]
      simp only [gates, List.flatMap_append]
      rw [list_append_matrix]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.getElem_ofFn]
      rfl

def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty (layout width) :=
  swapPrefix width width le_rfl

/-- The full physical operator is unchanged, including every spectator and every phase. -/
lemma program_matrix (width : Nat) :
    ((program width).matrix environment) =
      ((EncodedBit.Word.swapProgram (QubitLayout.canonical _) .empty
        (accumulator width) (numerator width)
        (fun index => accumulator_numerator_ne width index index)).matrix environment) := by
  rw [program, prefix_matrix, EncodedBit.Word.swapProgram]
  apply congrArg (fun instructions : List (EncodedBit.GateSpec (frameEncoding width)) =>
    ((EncodedBit.GateSpec.programList (QubitLayout.canonical _) .empty instructions).matrix
      environment))
  change gates width ((List.ofFn fun index : Fin width => index).take width) =
    gates width (List.ofFn fun index : Fin width => index)
  exact congrArg (gates width)
    (List.take_of_length_le (by simp only [List.length_ofFn, Nat.le_refl]))

lemma program_eventTrace (width : Nat) :
    (program width).eventTrace = List.replicate (3 * width)
      (Resource.Event.gate (model := .quantum AlgorithmGate.model .empty) .cnot) := by
  rw [program, swapPrefix, UnitaryCircuit.embed_eventTrace, word_eventTrace]

lemma program_depth (width : Nat) :
    (program width).evaluatedEventDepth (fun _ => 1) = if width = 0 then 0 else 3 := by
  simpa only [program, swapPrefix, UnitaryCircuit.evaluatedEventDepth,
    UnitaryCircuit.embed_eventDepth] using word_depth width width le_rfl

end

end QuantumAlg.MeasuredUncompute.FrameSwapParallel
