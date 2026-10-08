/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.InPlace.Forward
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.InitializationResources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.MicrostepResources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.ClockDecode.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Inverse

/-!
# Independent resources for complete shared-EEA forward and clean inverse programs

The fixed microstep count is the independently proved quotient-potential
schedule, followed by every actual full-clock decoder sweep and output
correction [LYL+26, app_proof/sub_stepnum.tex:4-16;
LYL+26, sec_EEA/sub_4phase.tex:107-128]. The in-place interface additionally
charges its real initial X load, physical output swaps, and terminal X
unload [LYL+26, sec_point_add/sec_point_add.tex:51-79].

All envelopes below are width-only arithmetic expressions. Every component
comparison uses the actual program's native event pool; unit depth is
bounded from the same program. The separate clean-XOR inverse includes
its separate output and both complete passes, whereas the in-place
forward interface has neither that copy nor that extra register.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.ForwardResources

noncomputable section

open NumberTheory.SharedEEA

/-- Independently bounded initialization, fixed repetitions, full decoder, and output correction. -/
def correctedBound (width : Nat) : Nat :=
  InitializationResources.bound width + 4 * (2 * width - 1) * MicrostepResources.bound width +
    ClockDecodeResources.count width + Addition.Gidney.biFlipEventBound (width + 3) + 2

/-- The in-place forward additionally executes fixed X loading and actual output SWAP/X gates. -/
def inPlaceBound (width : Nat) : Nat :=
  width + 3 + correctedBound width + 3 * ((width + 3) / 2) + width + 3

/-- The separate XOR interface computes, copies n bits, and reverses the entire computation. -/
def xorBound (width : Nat) : Nat := 2 * correctedBound width + width

private theorem native_count (modulus : Nat) (nontrivial : 1 < modulus) :
    (NativeSchedule.program modulus nontrivial).eventCost.card ≤
      InitializationResources.bound modulus.size +
        4 * (2 * modulus.size - 1) * MicrostepResources.bound modulus.size := by
  have initial := (InitializationResources.program_resources modulus).1
  have body := (MicrostepResources.program_resources modulus.size
    (PredicateLayout.modulus_length_width modulus nontrivial)).1
  have repeated := Nat.mul_le_mul_left (4 * (2 * modulus.size - 1)) body
  rw [NativeSchedule.program, UnitaryCircuit.seq_eventCost, Multiset.card_add,
    UnitaryCircuit.iterate_eventCost, Multiset.card_nsmul]
  change _ + 4 * (2 * modulus.size - 1) * _ ≤ _
  exact Nat.add_le_add initial repeated

private theorem correction_count (modulus : Nat) :
    (OutputCorrection.program modulus).eventCost.card ≤
      Addition.Gidney.biFlipEventBound (modulus.size + 3) + 2 := by
  rw [OutputCorrection.program_eventCost, OutputCorrectionFocus.program_event_count]
  exact Nat.add_le_add_right (Addition.Gidney.gidneyBiFlip_event_count_bound
    (FoldSourceProgram.wordWidth modulus) (FoldSourceProgram.reflectionPivot modulus)) 2

/-- The complete corrected native forward meets the width-only event envelope. -/
theorem corrected_count (modulus : Nat) (nontrivial : 1 < modulus) :
    (CorrectedSchedule.program modulus nontrivial).eventCost.card ≤
      correctedBound modulus.size := by
  have native := native_count modulus nontrivial
  have decoder := ClockDecodeResources.program_event_count modulus.size
  have correction := correction_count modulus
  rw [CorrectedSchedule.program, DecodedSchedule.program,
    UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    OutputCorrection.outputCorrection_nativeProgram_eventCost, Multiset.card_add, Multiset.card_add]
  unfold correctedBound
  omega

/-- The corrected forward's actual strict unit depth satisfies the same independent envelope. -/
theorem corrected_depth (modulus : Nat) (nontrivial : 1 < modulus) :
    (CorrectedSchedule.program modulus nontrivial).evaluatedEventDepth (fun _ => 1) ≤
      correctedBound modulus.size :=
  (ShiftResources.unitDepth_le_count _).trans (corrected_count modulus nontrivial)

/-- The in-place program includes all load, computation, orientation, and unload events. -/
theorem inPlace_count (modulus : Nat) (nontrivial : 1 < modulus) :
    (InPlaceForward.program modulus nontrivial).eventCost.card ≤ inPlaceBound modulus.size := by
  have load := (InitialPortProgram.program_resources modulus).1
  have corrected := corrected_count modulus nontrivial
  have ports := (OutputPortProgram.program_resources modulus).1
  rw [InPlaceForward.program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    Multiset.card_add, Multiset.card_add]
  unfold inPlaceBound
  omega

/-- No physical data permutation or history cleanup is omitted from the in-place depth bound. -/
theorem inPlace_depth (modulus : Nat) (nontrivial : 1 < modulus) :
    (InPlaceForward.program modulus nontrivial).evaluatedEventDepth (fun _ => 1) ≤
      inPlaceBound modulus.size :=
  (ShiftResources.unitDepth_le_count _).trans (inPlace_count modulus nontrivial)

/-- Replacing the large workspace port does not remove any event from the same complete dagger. -/
theorem inPlace_dagger_count (modulus : Nat) (nontrivial : 1 < modulus) :
    ((InPlaceForward.program modulus nontrivial).dagger
      (AlgorithmGate.oracleFreeAdjoints .empty)).eventCost.card ≤
      inPlaceBound modulus.size := by
  rw [AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost]
  change (Multiset.map (AlgorithmGate.oracleFreeEvent .empty)
    (InPlaceForward.program modulus nontrivial).eventCost).card ≤ _
  rw [Multiset.card_map]
  exact inPlace_count modulus nontrivial

/-- The separate clean-XOR inverse charges both full passes and the actual n CNOT copy. -/
theorem xor_count (modulus : Nat) (nontrivial : 1 < modulus) :
    (NativeInverse.program modulus nontrivial).eventCost.card ≤ xorBound modulus.size := by
  have corrected := corrected_count modulus nontrivial
  have copy := (OutputCopy.program_serial_resources modulus.size).1
  have forward : (NativeInverse.forwardProgram modulus nontrivial).eventCost.card =
      (CorrectedSchedule.program modulus nontrivial).eventCost.card := by
    rfl
  rw [NativeInverse.program, UnitaryCircuit.seq_eventCost, UnitaryCircuit.seq_eventCost,
    Multiset.card_add, Multiset.card_add,
    AlgorithmGate.algorithmGate_oracleFreeAdjoints_eventCost]
  change _ + (_ + (Multiset.map (AlgorithmGate.oracleFreeEvent .empty)
    (NativeInverse.forwardProgram modulus nontrivial).eventCost).card) ≤ _
  rw [Multiset.card_map, forward]
  unfold xorBound
  omega

/-- The clean-XOR program's strict unit depth is bounded from its same actual event pool. -/
theorem xor_depth (modulus : Nat) (nontrivial : 1 < modulus) :
    (NativeInverse.program modulus nontrivial).evaluatedEventDepth (fun _ => 1) ≤
      xorBound modulus.size :=
  (ShiftResources.unitDepth_le_count _).trans (xor_count modulus nontrivial)

end

end QuantumAlg.MAU.Inversion.SharedEEA.ForwardResources
