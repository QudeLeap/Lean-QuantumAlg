/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Nonzero
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Enable.Reference
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Unlookup
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# The genuine second-difference normal selector on the original bank

F560 is the whole-digit enable. N837 is toggled by F AND X-nonzero, using
all 256 actual X bits and W838 as arbitrary restored work. W is the other
coherent stream top and is never assumed clean. The inverse only clears N
when the same F and X predicate is present again; bad labels are not given
an unsupported cleanup promise.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Normal

noncomputable section

open QuantumAlg.EncodedBit

/-- Actual X payload, normal output and arbitrary other-stream top work. -/
def layout : Word.OneDirtyLayout (encoding := Window.encoding) 256 where
  source := Window.resultWord .work2
  output := Window.normalBit
  work := Window.secondStreamBit
  source_injective := Window.resultWord_distinct .work2
  source_output_ne := by
    intro index same
    have positions := congrArg Fin.val same
    rw [Window.resultWord_wire, Window.normalBit_wire] at positions
    change 259 + index.val = 837 at positions
    have bound := index.isLt
    omega
  source_work_ne := by
    intro index same
    have positions := congrArg Fin.val same
    rw [Window.resultWord_wire, Window.secondStreamBit_wire] at positions
    change 259 + index.val = 838 at positions
    have bound := index.isLt
    omega
  work_output_ne := by
    intro same
    have positions := congrArg Fin.val same
    rw [Window.secondStreamBit_wire, Window.normalBit_wire] at positions
    omega

lemma flag_sources (index : Fin 256) :
    Window.Enable.outputBit.wire ≠ (layout.source.bit index).wire := by
  intro same
  have positions := congrArg Fin.val same
  change Window.Enable.outputBit.wire.val =
    ((Window.resultWord .work2).bit index).wire.val at positions
  rw [Window.Enable.outputBit_wire, Window.resultWord_wire] at positions
  change 560 = 259 + index.val at positions
  have bound := index.isLt
  omega

lemma flag_output : Window.Enable.outputBit.wire ≠ layout.output.wire := by
  intro same
  have positions := congrArg Fin.val same
  change Window.Enable.outputBit.wire.val = Window.normalBit.wire.val at positions
  rw [Window.Enable.outputBit_wire, Window.normalBit_wire] at positions
  omega

lemma flag_work : Window.Enable.outputBit.wire ≠ layout.work.wire := by
  intro same
  have positions := congrArg Fin.val same
  change Window.Enable.outputBit.wire.val = Window.secondStreamBit.wire.val at positions
  rw [Window.Enable.outputBit_wire, Window.secondStreamBit_wire] at positions
  omega

def selected (state : Window.Raw) : Bool :=
  layout.controlledNonzero Window.Enable.outputBit state

def step : Window.Raw → Window.Raw :=
  layout.controlledNonzeroStep Window.Enable.outputBit

def gates : List (GateSpec Window.encoding) :=
  layout.controlledNonzeroGates Window.Enable.outputBit flag_sources flag_output flag_work

def program : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical Window.encoding.width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty gates

def inverseProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical Window.encoding.width).toQuantum :=
  GateSpec.programList (QubitLayout.canonical _) .empty gates.reverse

lemma gates_step (state : Window.Raw) : GateSpec.stepList gates state = step state :=
  layout.controlledNonzeroGates_step Window.Enable.outputBit flag_sources flag_output flag_work
    state

lemma gates_reverse_step (state : Window.Raw) :
    GateSpec.stepList gates.reverse state = step state :=
  layout.controlledNonzeroGates_reverse_step Window.Enable.outputBit flag_sources flag_output
    flag_work state

lemma step_step (state : Window.Raw) : step (step state) = state :=
  layout.controlledNonzeroStep_step Window.Enable.outputBit flag_output state

lemma step_other (observed : EncodedBit Window.encoding)
    (outside : Window.normalBit.wire ≠ observed.wire) (state : Window.Raw) :
    observed.get (step state) = observed.get state :=
  layout.controlledNonzeroStep_other Window.Enable.outputBit observed outside state

lemma step_normal (state : Window.Raw) :
    Window.normalBit.get (step state) = (Window.normalBit.get state ^^ selected state) :=
  layout.controlledNonzeroStep_output Window.Enable.outputBit state

/-- N starts clean at the concrete entry, while every work/source value is arbitrary. -/
lemma step_normal_of_zero (state : Window.Raw) (zero : Window.normalBit.get state = false) :
    Window.normalBit.get (step state) = selected state := by
  rw [step_normal, zero, Bool.false_xor]

/-- Cleanup requires the original predicate to be present at this actual reverse call. -/
lemma step_normal_of_match (state : Window.Raw)
    (matched : Window.normalBit.get state = selected state) :
    Window.normalBit.get (step state) = false := by
  rw [step_normal, matched, Bool.xor_self]

lemma step_work (state : Window.Raw) :
    Window.secondStreamBit.get (step state) = Window.secondStreamBit.get state :=
  step_other Window.secondStreamBit layout.work_output_ne.symm state

lemma step_flag (state : Window.Raw) :
    Window.Enable.outputBit.get (step state) = Window.Enable.outputBit.get state :=
  step_other Window.Enable.outputBit flag_output.symm state

/-- The entire physical complement, including both coherent stream tops, is retained. -/
lemma step_address (index : Fin 15) (state : Window.Raw) :
    (Window.addressBit index).get (step state) = (Window.addressBit index).get state := by
  apply step_other
  intro same
  have positions := congrArg Fin.val same
  rw [Window.normalBit_wire, Window.addressBit_wire] at positions
  omega

private lemma value_zero_iff {width : Nat} (value : Fin (2 ^ width)) :
    (∀ index : Fin width, value.val.testBit index.val = false) ↔
      value = ⟨0, Nat.two_pow_pos width⟩ := by
  constructor
  · intro zero
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    simpa only [Fin.val_zero, Nat.zero_testBit] using zero index
  · intro zero index
    rw [zero]
    simp only [Nat.zero_testBit]

lemma selected_value (state : Window.Raw) :
    selected state = (Window.Enable.outputBit.get state &&
      !decide (Frame.work2 state.1 = (⟨0, Nat.two_pow_pos 256⟩ : Fin (2 ^ 256)))) := by
  have reads : layout.PatternMatches (fun _ => false) state ↔
      ∀ index : Fin 256, (Frame.work2 state.1).val.testBit index.val = false := by
    apply forall_congr'
    intro index
    change (Window.pointBit (WordPort.bit .work2 index)).get state = false ↔ _
    rw [Window.pointBit_get, WordPort.bit_get]
    rfl
  change (Window.Enable.outputBit.get state &&
    !decide (layout.PatternMatches (fun _ => false) state)) = _
  apply congrArg (fun value : Bool => Window.Enable.outputBit.get state && !value)
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact reads.trans (value_zero_iff (Frame.work2 state.1))

lemma program_apply (environment : OracleModel.empty.Interpretation) (state : Window.Raw) :
    program.applyNormalized environment (Window.ket state) = Window.ket (step state) := by
  have actual := GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty gates gates_step
    environment
  exact actual.apply_encoded_ket state

lemma inverseProgram_apply (environment : OracleModel.empty.Interpretation) (state : Window.Raw) :
    inverseProgram.applyNormalized environment (Window.ket state) = Window.ket (step state) :=
  (GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty gates.reverse
    gates_reverse_step environment).apply_encoded_ket state

/-- All original and external correlations, including coherent F and dirty W, are retained. -/
lemma program_reference (environment : OracleModel.empty.Interpretation)
    {Reference : Register} {Index : Type} [Fintype Index] (states : Index → Window.Raw)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec
      (Window.Enable.referenceOperator program environment Reference)
      (Window.referenceVector states reference amplitude) =
      Window.referenceVector (fun index => step (states index)) reference amplitude :=
  Native.reference_sum_of_actual program environment _ _
    (fun index => program_apply environment (states index)) reference amplitude

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain.Normal
