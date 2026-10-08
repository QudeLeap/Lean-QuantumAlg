/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Frame.Ports
import all QuantumAlg.Components.Encoded.BitGates.Word.Swap

/-!
# The actual final A/Y swap in measured arithmetic

The literal three-CNOT swap per bit puts the computed result into the
original Y word. X and every retained history wire remain unchanged.
This is an executed gate list with its full native charge, as required
after phase correction [LYL+26, sec_point_add/sec_point_add.tex:101-105].
-/

namespace QuantumAlg.MeasuredUncompute.FrameSwap

noncomputable section

open EncodedBit ProductPlacement FramePorts

private theorem separation (width : Nat) (index : Fin width) :
    ((accumulator width).bit index).wire ≠ ((numerator width).bit index).wire :=
  accumulator_numerator_ne width index index

private def body (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (frameEncoding width).width).toQuantum :=
  Word.swapProgram (QubitLayout.canonical _) .empty
    (accumulator width) (numerator width) (separation width)

/-- The exact literal swap retains the complete original frame after its last actual CNOT. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (frameEncoding width).width).toQuantum :=
  body width

/-- Complete action of the actual bitwise swap, including every complementary field. -/
def step (width : Nat) : Frame width → Frame width :=
  Word.swapStep (accumulator width) (numerator width) (separation width)

/-- Full coherent basis semantics comes from the same actual three-CNOT gate list. -/
theorem frameSwap_realizes (width : Nat) :
    UnitaryCircuit.Realizes (frameEncoding width) (program width) (step width) :=
  Word.swap_realizes (QubitLayout.canonical _) .empty
    (accumulator width) (numerator width) (separation width)

/-- A receives each original Y bit at the matching physical word position. -/
theorem frameSwap_accumulator (width : Nat) (index : Fin width) (state : Frame width) :
    ((accumulator width).bit index).get (step width state) =
      ((numerator width).bit index).get state :=
  Word.swapStep_get_left (accumulator width) (numerator width) (separation width) index
    (fun other different => accumulator_distinct width other index different)
    (fun other => (accumulator_numerator_ne width index other).symm)
    (fun other => accumulator_numerator_ne width other index)
    (fun other different => numerator_distinct width other index different) state

/-- Y receives each computed A bit at the matching original output position. -/
theorem frameSwap_numerator (width : Nat) (index : Fin width) (state : Frame width) :
    ((numerator width).bit index).get (step width state) =
      ((accumulator width).bit index).get state :=
  Word.swapStep_get_right (accumulator width) (numerator width) (separation width) index
    (fun other different => accumulator_distinct width other index different)
    (fun other => (accumulator_numerator_ne width index other).symm)
    (fun other => accumulator_numerator_ne width other index)
    (fun other different => numerator_distinct width other index different) state

/-- The complete original X input remains unchanged by the final result swap. -/
theorem frameSwap_input (width : Nat) (index : Fin width) (state : Frame width) :
    ((input width).bit index).get (step width state) = ((input width).bit index).get state :=
  Word.swapStep_get_observed_of_swap_ne (accumulator width) (numerator width)
    (separation width) ((input width).bit index)
    (fun other => ((input_separate width index other).1).symm)
    (fun other => ((input_separate width index other).2).symm) state

/-- Every retained wire outside the two exchanged ports keeps its original value. -/
theorem frameSwap_other (width : Nat) (observed : EncodedBit (frameEncoding width))
    (outsideA : ∀ index, ((accumulator width).bit index).wire ≠ observed.wire)
    (outsideY : ∀ index, ((numerator width).bit index).wire ≠ observed.wire)
    (state : Frame width) : observed.get (step width state) = observed.get state :=
  Word.swapStep_get_observed_of_swap_ne (accumulator width) (numerator width)
    (separation width) observed outsideA outsideY state

/-- The actual final swap retains all original large and small quantum fields. -/
theorem frameSwap_physical (width : Nat) :
    (QubitLayout.canonical (frameEncoding width).width).systemIdx =
      List.range (frameEncoding width).width :=
  QubitLayout.canonical_systemIdx _

/-- Every one of the three actual CNOTs per exchanged bit is charged. -/
theorem frameSwap_cnot_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (program width).eventCost = 3 * width := by
  exact Word.swapCircuit_cnot_eventCount (QubitLayout.canonical _) .empty
    (accumulator width) (numerator width) (separation width)

/-- No additional event is hidden beside the literal three-CNOT swaps. -/
theorem frameSwap_event_count (width : Nat) : (program width).eventCost.card = 3 * width := by
  change (GateSpec.programList (QubitLayout.canonical _) .empty
    (Word.swapGates (accumulator width) (numerator width) (separation width))).eventCost.card = _
  rw [GateSpec.programList_eventCost_card, Word.swapGates_length]

/-- Actual unit-duration serial depth includes the complete final word exchange. -/
theorem frameSwap_depth (width : Nat) :
    (program width).evaluatedEventDepth (fun _ => 1) = 3 * width := by
  exact Word.swapCircuit_unit_eventDepth (QubitLayout.canonical _) .empty
    (accumulator width) (numerator width) (separation width)

end

end QuantumAlg.MeasuredUncompute.FrameSwap
