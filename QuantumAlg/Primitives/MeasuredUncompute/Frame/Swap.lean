/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Ports
import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Swap.Parallel
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap

/-!
# The actual final A/Y swap in measured arithmetic

The three-CNOT swap per bit puts the computed result into the
original Y word. X and every retained history wire remain unchanged.
Disjoint pairs execute in parallel with the same full native charge, as required
after phase correction [LYL+26, sec_point_add/sec_point_add.tex:101-105].
-/

namespace QuantumAlg.MeasuredUncompute.FrameSwap

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open EncodedBit ProductPlacement FramePorts

private lemma separation (width : Nat) (index : Fin width) :
    ((accumulator width).bit index).wire ≠ ((numerator width).bit index).wire :=
  accumulator_numerator_ne width index index

/-- The exact literal swap retains the complete original frame after its last actual CNOT. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (frameEncoding width).width).toQuantum :=
  FrameSwapParallel.program width

/-- Complete action of the actual bitwise swap, including every complementary field. -/
def step (width : Nat) : Frame width → Frame width :=
  Word.swapStep (accumulator width) (numerator width) (separation width)

/-- Full coherent basis semantics comes from the same actual three-CNOT gate list. -/
lemma frameSwap_realizes (width : Nat) :
    UnitaryCircuit.Realizes (frameEncoding width) (program width) environment (step width) where
  apply_encoded_ket state := by
    change ((FrameSwapParallel.program width).matrix environment).apply _ = _
    rw [FrameSwapParallel.program_matrix]
    exact (Word.swap_realizes (QubitLayout.canonical _) .empty
      (accumulator width) (numerator width) (separation width)).apply_encoded_ket state

/-- A receives each original Y bit at the matching physical word position. -/
lemma frameSwap_accumulator (width : Nat) (index : Fin width) (state : Frame width) :
    ((accumulator width).bit index).get (step width state) =
      ((numerator width).bit index).get state :=
  Word.swapStep_get_left (accumulator width) (numerator width) (separation width) index
    (fun other different => accumulator_distinct width other index different)
    (fun other => (accumulator_numerator_ne width index other).symm)
    (fun other => accumulator_numerator_ne width other index)
    (fun other different => numerator_distinct width other index different) state

/-- Y receives each computed A bit at the matching original output position. -/
lemma frameSwap_numerator (width : Nat) (index : Fin width) (state : Frame width) :
    ((numerator width).bit index).get (step width state) =
      ((accumulator width).bit index).get state :=
  Word.swapStep_get_right (accumulator width) (numerator width) (separation width) index
    (fun other different => accumulator_distinct width other index different)
    (fun other => (accumulator_numerator_ne width index other).symm)
    (fun other => accumulator_numerator_ne width other index)
    (fun other different => numerator_distinct width other index different) state

/-- The complete original X input remains unchanged by the final result swap. -/
lemma frameSwap_input (width : Nat) (index : Fin width) (state : Frame width) :
    ((input width).bit index).get (step width state) = ((input width).bit index).get state :=
  Word.swapStep_get_observed_of_swap_ne (accumulator width) (numerator width)
    (separation width) ((input width).bit index)
    (fun other => ((input_separate width index other).1).symm)
    (fun other => ((input_separate width index other).2).symm) state

/-- Every retained wire outside the two exchanged ports keeps its original value. -/
lemma frameSwap_other (width : Nat) (observed : EncodedBit (frameEncoding width))
    (outsideA : ∀ index, ((accumulator width).bit index).wire ≠ observed.wire)
    (outsideY : ∀ index, ((numerator width).bit index).wire ≠ observed.wire)
    (state : Frame width) : observed.get (step width state) = observed.get state :=
  Word.swapStep_get_observed_of_swap_ne (accumulator width) (numerator width)
    (separation width) observed outsideA outsideY state

/-- The actual final swap retains all original large and small quantum fields. -/
lemma frameSwap_physical (width : Nat) :
    (QubitLayout.canonical (frameEncoding width).width).systemIdx =
      List.range (frameEncoding width).width :=
  QubitLayout.canonical_systemIdx _

/-- The complete native ledger contains exactly three CNOTs per exchanged bit. -/
lemma frameSwap_eventCost (width : Nat) :
    (program width).eventCost = (3 * width) • ResourcePool.singleton
      (model := .quantum AlgorithmGate.model .empty) (.gate .cnot) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    program, FrameSwapParallel.program_eventTrace, ResourcePool.ofList_replicate]
  rfl

/-- Every one of the three actual CNOTs per exchanged bit is charged. -/
lemma frameSwap_cnot_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (program width).eventCost = 3 * width := by
  rw [frameSwap_eventCost, ResourcePool.count_nsmul, ResourcePool.count_singleton_self, mul_one]

/-- No additional event is hidden beside the literal three-CNOT swaps. -/
lemma frameSwap_event_count (width : Nat) : (program width).eventCost.card = 3 * width := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost,
    program, FrameSwapParallel.program_eventTrace]
  simp [ResourcePool.ofList]

/-- All nonempty disjoint word exchanges execute in three actual CNOT layers. -/
lemma frameSwap_depth (width : Nat) :
    (program width).evaluatedEventDepth (fun _ => 1) = if width = 0 then 0 else 3 :=
  FrameSwapParallel.program_depth width

end

end QuantumAlg.MeasuredUncompute.FrameSwap
