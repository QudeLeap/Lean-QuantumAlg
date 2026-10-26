/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Native.BorrowedControl
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Inversion.Normal
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Paid transfer of the window enable to the actual resident N control

F is original pool system 560; N is original external system 837. The actual
digit toggle is reversed after copying F into N, so a clean original pool is
fully zero before the resident program. The same paid toggle and CNOT return
the temporary N after the resident stage. The real second normal selector is
not identified with the whole-digit predicate by this construction.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Control

noncomputable section

open QuantumAlg.EncodedBit Window

private lemma toggle_flip_comm {Data : Type} {encoding : BinaryLabelEncoding Data}
    {count : Nat} (ports : Word.OneDirtyLayout (encoding := encoding) count)
    (observed : EncodedBit encoding)
    (sourceNe : ∀ index, observed.wire ≠ (ports.source.bit index).wire) (state : Data) :
    Enable.toggleStep ports (observed.flip state) =
      observed.flip (Enable.toggleStep ports state) := by
  have unchanged : (∀ index, (ports.source.bit index).get (observed.flip state) = false) ↔
      (∀ index, (ports.source.bit index).get state = false) := by
    apply forall_congr'
    intro index
    rw [get_flip_of_wire_ne observed (ports.source.bit index) (sourceNe index)]
  dsimp only [Enable.toggleStep]
  by_cases zero : ∀ index, (ports.source.bit index).get state = false
  · rw [if_pos (unchanged.mpr zero), if_pos zero]
  · have noMatch : ¬ ∀ index, (ports.source.bit index).get (observed.flip state) = false :=
      fun matched => zero (unchanged.mp matched)
    rw [if_neg noMatch, if_neg zero]
    exact flip_comm ports.output observed state

lemma flag_get (state : Window.Raw) :
    Enable.outputBit.get state = Native.BorrowedControl.flag.get state.1 := rfl

lemma flag_normal_ne : Enable.outputBit.wire ≠ Window.normalBit.wire := by
  intro same
  have positions := congrArg Fin.val same
  rw [Enable.outputBit_wire, Window.normalBit_wire] at positions
  omega

private lemma normal_digit_ne (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) :
    Window.normalBit.wire ≠ (Enable.digitBit stream width bounded index).wire := by
  intro same
  have positions := congrArg Fin.val same
  rw [Window.normalBit_wire, Enable.digitBit_wire] at positions
  split_ifs at positions <;> omega

def digitEnabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) : Bool :=
  !decide (∀ index, (Enable.digitBit stream width bounded index).get state = false)

def copyGate : GateSpec Window.encoding :=
  .cnot Enable.outputBit Window.normalBit flag_normal_ne

def copyStep : Window.Raw → Window.Raw := cnotStep Enable.outputBit Window.normalBit

lemma copyStep_flag (state : Window.Raw) :
    Enable.outputBit.get (copyStep state) = Enable.outputBit.get state :=
  cnotStep_get_of_target_ne _ _ _ flag_normal_ne.symm state

lemma copyStep_normal (state : Window.Raw) :
    Window.normalBit.get (copyStep state) =
      (Window.normalBit.get state ^^ Enable.outputBit.get state) :=
  cnotStep_get_target _ _ state

lemma digitEnabled_copy (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    digitEnabled stream width bounded (copyStep state) =
      digitEnabled stream width bounded state := by
  unfold digitEnabled
  simp only [copyStep, cnotStep_get_of_target_ne Enable.outputBit Window.normalBit
    (Enable.digitBit stream width bounded _) (normal_digit_ne stream width bounded _)]

lemma toggle_normal_comm (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    Enable.step stream width bounded (Window.normalBit.flip state) =
      Window.normalBit.flip (Enable.step stream width bounded state) :=
  toggle_flip_comm (Enable.layout stream width bounded) Window.normalBit
    (normal_digit_ne stream width bounded) state

def prepareGates (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    List (GateSpec Window.encoding) :=
  [copyGate] ++ (Enable.gates stream width bounded).reverse

def restoreGates (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    List (GateSpec Window.encoding) :=
  Enable.gates stream width bounded ++ [copyGate]

def prepareStep (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) : Window.Raw :=
  Enable.step stream width bounded (copyStep state)

def restoreStep (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) : Window.Raw :=
  copyStep (Enable.step stream width bounded state)

def prepareProgram (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (prepareGates stream width bounded)

def restoreProgram (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (restoreGates stream width bounded)

lemma prepareGates_step (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    GateSpec.stepList (prepareGates stream width bounded) state =
      prepareStep stream width bounded state := by
  rw [prepareGates, GateSpec.stepList_append]
  change GateSpec.stepList (Enable.toggleGates (Enable.layout stream width bounded)).reverse
    (copyStep state) = prepareStep stream width bounded state
  rw [Enable.toggleGates_reverse_step]
  rfl

lemma restoreGates_step (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) :
    GateSpec.stepList (restoreGates stream width bounded) state =
      restoreStep stream width bounded state := by
  rw [restoreGates, GateSpec.stepList_append]
  change copyStep (GateSpec.stepList (Enable.toggleGates (Enable.layout stream width bounded))
    state) = _
  rw [Enable.toggleGates_step]
  rfl

lemma prepare_realizes (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes Window.encoding (prepareProgram stream width bounded) environment
      (prepareStep stream width bounded) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (prepareGates_step stream width bounded) environment

lemma restore_realizes (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes Window.encoding (restoreProgram stream width bounded) environment
      (restoreStep stream width bounded) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (restoreGates_step stream width bounded) environment

/-- The exact complete state has F restored; only the temporary external N may be flipped. -/
lemma prepare_after_enable (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) (clean : Frame.CleanPool state.1) :
    prepareStep stream width bounded (Enable.step stream width bounded state) =
      if digitEnabled stream width bounded state then Window.normalBit.flip state else state := by
  have flag : Enable.outputBit.get (Enable.step stream width bounded state) =
      digitEnabled stream width bounded state :=
    Enable.step_output_of_zero stream width bounded state (Enable.outputBit_clean state clean)
  unfold prepareStep copyStep cnotStep
  rw [flag]
  split
  · exact (toggle_normal_comm stream width bounded _).trans
      (congrArg Window.normalBit.flip (Enable.step_step stream width bounded state))
  · exact Enable.step_step stream width bounded state

/-- All twenty-one actual pool systems are zero when the N-selected resident body starts. -/
lemma prepare_after_enable_cleanPool (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) (clean : Frame.CleanPool state.1) :
    Frame.CleanPool
      (prepareStep stream width bounded (Enable.step stream width bounded state)).1 := by
  rw [prepare_after_enable stream width bounded state clean]
  split
  · exact clean
  · exact clean

/-- Temporary N is the complete digit predicate, independently of its address MSB. -/
lemma prepare_after_enable_normal (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) (clean : Frame.CleanPool state.1)
    (normalZero : Window.normalBit.get state = false) :
    Window.normalBit.get
      (prepareStep stream width bounded (Enable.step stream width bounded state)) =
        digitEnabled stream width bounded state := by
  rw [prepare_after_enable stream width bounded state clean]
  cases enabled : digitEnabled stream width bounded state <;>
    simp only [Bool.false_eq_true, if_false, if_true, get_flip_self,
      normalZero, Bool.not_false]

/-- Every physical coordinate outside F and N keeps its original value through the prefix. -/
lemma prepare_other (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (observed : EncodedBit Window.encoding) (outsideF : Enable.outputBit.wire ≠ observed.wire)
    (outsideN : Window.normalBit.wire ≠ observed.wire) (state : Window.Raw) :
    observed.get (prepareStep stream width bounded state) = observed.get state :=
  (Enable.step_other stream width bounded observed outsideF (copyStep state)).trans
    (cnotStep_get_of_target_ne _ _ observed outsideN state)

lemma restore_flag (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) (zero : Enable.outputBit.get state = false) :
    Enable.outputBit.get (restoreStep stream width bounded state) =
      digitEnabled stream width bounded state :=
  (copyStep_flag (Enable.step stream width bounded state)).trans
    (Enable.step_output_of_zero stream width bounded state zero)

/-- The same paid toggle/CNOT clears temporary N and returns the original live digit enable. -/
lemma restore_normal_zero (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (state : Window.Raw) (zero : Enable.outputBit.get state = false)
    (normal : Window.normalBit.get state = digitEnabled stream width bounded state) :
    Window.normalBit.get (restoreStep stream width bounded state) = false := by
  have flag : Enable.outputBit.get (Enable.step stream width bounded state) =
      digitEnabled stream width bounded state :=
    Enable.step_output_of_zero stream width bounded state zero
  exact (copyStep_normal (Enable.step stream width bounded state)).trans
    ((congrArg₂ Bool.xor (Enable.step_other stream width bounded Window.normalBit
      flag_normal_ne state) flag).trans (by rw [normal, Bool.xor_self]))

lemma restore_other (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (observed : EncodedBit Window.encoding) (outsideF : Enable.outputBit.wire ≠ observed.wire)
    (outsideN : Window.normalBit.wire ≠ observed.wire) (state : Window.Raw) :
    observed.get (restoreStep stream width bounded state) = observed.get state :=
  (cnotStep_get_of_target_ne _ _ observed outsideN
    (Enable.step stream width bounded state)).trans
      (Enable.step_other stream width bounded observed outsideF state)

/-- The middle body is the actual accepted N-selected resident inversion on the same 854 systems. -/
def firstResidentProgram (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical Window.encoding.width).toQuantum :=
  (prepareProgram stream width bounded).seq
    ((Window.suffixProgram Inversion.Normal.program).seq (restoreProgram stream width bounded))

end

end Control

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
