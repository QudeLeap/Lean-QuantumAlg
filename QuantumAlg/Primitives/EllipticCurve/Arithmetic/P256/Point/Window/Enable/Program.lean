/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Ports
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern

/-!
# Paid whole-digit nonzero toggle and its literal inverse

The generic complete-label composition is proved before the16/4-control
instances. Both directions act on every input label, including an arbitrary
incoming enable and arbitrary borrowed work. Initialization is needed only
when interpreting the enable output as the predicate itself.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable

noncomputable section

open QuantumAlg.EncodedBit

variable {Data : Type} {dataEncoding : BinaryLabelEncoding Data} {controls : Nat}

def toggleGates (ports : Word.OneDirtyLayout (encoding := dataEncoding) controls) :
    List (GateSpec dataEncoding) :=
  [.x ports.output] ++ ports.patternGates (fun _ => false)

def toggleStep (ports : Word.OneDirtyLayout (encoding := dataEncoding) controls)
    (state : Data) : Data :=
  if ∀ index, (ports.source.bit index).get state = false then state else ports.output.flip state

lemma toggleGates_step (ports : Word.OneDirtyLayout (encoding := dataEncoding) controls)
    (state : Data) : GateSpec.stepList (toggleGates ports) state = toggleStep ports state := by
  rw [toggleGates, GateSpec.stepList_append]
  change GateSpec.stepList (ports.patternGates fun _ => false) (ports.output.flip state) = _
  rw [Word.OneDirtyLayout.patternGates_step]
  have invariant := ports.patternMatches_flip_output (fun _ => false) state
  by_cases zero : ∀ index, (ports.source.bit index).get state = false
  · rw [if_pos (invariant.mpr zero), EncodedBit.flip_flip, toggleStep, if_pos zero]
  · rw [if_neg (fun matched => zero (invariant.mp matched)), toggleStep, if_neg zero]

lemma toggleGates_reverse_step (ports : Word.OneDirtyLayout (encoding := dataEncoding) controls)
    (state : Data) :
    GateSpec.stepList (toggleGates ports).reverse state = toggleStep ports state := by
  rw [toggleGates, List.reverse_append, GateSpec.stepList_append,
    Word.OneDirtyLayout.patternGates_reverse_step]
  change ports.output.flip
    (if ports.PatternMatches (fun _ => false) state then ports.output.flip state else state) = _
  by_cases zero : ∀ index, (ports.source.bit index).get state = false
  · rw [if_pos zero, EncodedBit.flip_flip, toggleStep, if_pos zero]
  · rw [if_neg zero, toggleStep, if_neg zero]

lemma toggleStep_other (ports : Word.OneDirtyLayout (encoding := dataEncoding) controls)
    (observed : EncodedBit dataEncoding) (different : ports.output.wire ≠ observed.wire)
    (state : Data) : observed.get (toggleStep ports state) = observed.get state := by
  unfold toggleStep
  split
  · rfl
  · exact get_flip_of_wire_ne ports.output observed different state

lemma toggleStep_output (ports : Word.OneDirtyLayout (encoding := dataEncoding) controls)
    (state : Data) :
    ports.output.get (toggleStep ports state) =
      (ports.output.get state ^^
        !decide (∀ index, (ports.source.bit index).get state = false)) := by
  by_cases zero : ∀ index, (ports.source.bit index).get state = false
  · have decision : decide (∀ index, (ports.source.bit index).get state = false) = true :=
      decide_eq_true zero
    rw [toggleStep, if_pos zero, decision, Bool.not_true, Bool.xor_false]
  · have decision : decide (∀ index, (ports.source.bit index).get state = false) = false :=
      decide_eq_false zero
    rw [toggleStep, if_neg zero, decision, Bool.not_false, Bool.xor_true, get_flip_self]

def gates (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) : List (GateSpec encoding) :=
  toggleGates (layout stream width bounded)

def step (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) : Raw → Raw :=
  toggleStep (layout stream width bounded)

def program (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates stream width bounded)

/-- The inverse reverses this exact elementary list, including every source mask. -/
def inverseProgram (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty (gates stream width bounded).reverse

lemma program_realizes (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding (program stream width bounded) environment
      (step stream width bounded) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (toggleGates_step (layout stream width bounded)) environment

lemma inverseProgram_realizes (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding (inverseProgram stream width bounded) environment
      (step stream width bounded) :=
  GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty _
    (toggleGates_reverse_step (layout stream width bounded)) environment

lemma step_step (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Raw) :
    step stream width bounded (step stream width bounded state) = state := by
  have actual := GateSpec.stepList_reverse_stepList (gates stream width bounded) state
  dsimp only [gates] at actual
  rw [toggleGates_step, toggleGates_reverse_step] at actual
  exact actual

lemma step_output (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Raw) :
    outputBit.get (step stream width bounded state) =
      (outputBit.get state ^^
        !decide (∀ index, (digitBit stream width bounded index).get state = false)) :=
  toggleStep_output (layout stream width bounded) state

/-- Only this interpretation needs the actual enable system initialized to zero. -/
lemma step_output_of_zero (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Raw)
    (clean : outputBit.get state = false) :
    outputBit.get (step stream width bounded state) =
      !decide (∀ index, (digitBit stream width bounded index).get state = false) := by
  rw [step_output, clean, Bool.false_xor]

lemma step_other (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (observed : EncodedBit encoding) (different : outputBit.wire ≠ observed.wire)
    (state : Raw) : observed.get (step stream width bounded state) = observed.get state :=
  toggleStep_other (layout stream width bounded) observed different state

lemma step_work (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (state : Raw) :
    workBit.get (step stream width bounded state) = workBit.get state :=
  step_other stream width bounded workBit (layout stream width bounded).work_output_ne.symm state

lemma step_digit (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (index : Fin (width + 1)) (state : Raw) :
    (digitBit stream width bounded index).get (step stream width bounded state) =
      (digitBit stream width bounded index).get state :=
  step_other stream width bounded _
    ((layout stream width bounded).source_output_ne index).symm state

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Enable
