/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Active.Prefix
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Phase
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Coherent

/-!
# The actual active division call has the same measured-mask coefficient

The actual save, physical reset, reused adjoint, paid field-product phase
and unconditional numerical swap all remain present. The phase readouts
come from the complete real reused label and its retained control frontier.
No prefix, tail operator or arithmetic equation is supplied as a callback.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open MAU.Inversion.SharedEEA.Scanned
open Execution EncodedBit.WindowLookup NormalizedVector

private lemma prepare_word (port : WordPort) (stream : Fin 2) (width : Nat)
    (bounded : width ≤ 15) (state : Window.Raw) :
    port.value (Control.prepareStep stream width bounded state).1 = port.value state.1 :=
  window_word_eq_of_reads port _ state (fun index =>
    Control.prepare_other stream width bounded _ (window_word_control_ne port index).1
      (window_word_control_ne port index).2 state)

private def frontier (state : Window.Raw) : Pool 256 × (Frame.Controls × Window.Address) :=
  (state.1.1.1.2, (state.1.2, state.2))

private lemma enable_eq_of_pool (first second : Window.Raw)
    (same : first.1.1.1.2 = second.1.1.1.2) :
    (Phase.physicalSelector .enable).get first.1 =
      (Phase.physicalSelector .enable).get second.1 :=
  congrArg (fun value : Pool 256 => value.1.getMsbD 1) same


private lemma output_frontier (first second : Window.Raw)
    (same : frontier first = frontier second) :
    Window.Enable.outputBit.get first = Window.Enable.outputBit.get second :=
  (Control.flag_get first).trans
    ((enable_eq_of_pool first second (congrArg Prod.fst same)).trans
      (Control.flag_get second).symm)

private lemma frontier_normal_flip (first second : Window.Raw)
    (same : frontier first = frontier second) :
    frontier (Window.normalBit.flip first) = frontier (Window.normalBit.flip second) := by
  exact congrArg (fun value : Pool 256 × (Frame.Controls × Window.Address) =>
    (value.1, ((value.2.1.1, (!value.2.1.2.1, value.2.1.2.2)), value.2.2))) same

private lemma frontier_enable_flip (first second : Window.Raw)
    (same : frontier first = frontier second) :
    frontier (Window.Enable.outputBit.flip first) =
      frontier (Window.Enable.outputBit.flip second) := by
  rcases first with ⟨⟨⟨⟨firstSource, firstPool⟩, firstY⟩, firstFlags⟩, firstAddress⟩
  rcases second with ⟨⟨⟨⟨secondSource, secondPool⟩, secondY⟩, secondFlags⟩, secondAddress⟩
  have pool := congrArg Prod.fst same
  have flags := congrArg (fun value => value.2.1) same
  have address := congrArg (fun value => value.2.2) same
  change firstPool = secondPool at pool
  change firstFlags = secondFlags at flags
  change firstAddress = secondAddress at address
  cases pool
  cases flags
  cases address
  rfl

private lemma digit_frontier (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (first second : Window.Raw) (same : frontier first = frontier second)
    (index : Fin (width + 1)) :
    (Window.Enable.digitBit stream width bounded index).get first =
      (Window.Enable.digitBit stream width bounded index).get second := by
  refine Fin.cases ?_ (fun index => ?_) index
  · change (Window.streamBit stream).get first = (Window.streamBit stream).get second
    unfold Window.streamBit
    split
    · exact congrArg (fun value : Pool 256 × (Frame.Controls × Window.Address) =>
        value.2.1.1) same
    · exact congrArg (fun value : Pool 256 × (Frame.Controls × Window.Address) =>
        value.2.1.2.2) same
  · exact congrArg (fun value : Pool 256 × (Frame.Controls × Window.Address) =>
      value.2.2.val.testBit (14 - index.val)) same

private lemma restore_frontier_congr (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (first second : Window.Raw) (same : frontier first = frontier second) :
    frontier (Control.restoreStep stream width bounded first) =
      frontier (Control.restoreStep stream width bounded second) := by
  have enabled : frontier (Window.Enable.step stream width bounded first) =
      frontier (Window.Enable.step stream width bounded second) := by
    have matched :
        (∀ index, (Window.Enable.digitBit stream width bounded index).get first = false) ↔
        (∀ index, (Window.Enable.digitBit stream width bounded index).get second = false) :=
      forall_congr' (fun index => by
        rw [digit_frontier stream width bounded first second same index])
    change frontier (if ∀ index,
        (Window.Enable.digitBit stream width bounded index).get first = false then first
        else Window.Enable.outputBit.flip first) =
      frontier (if ∀ index,
        (Window.Enable.digitBit stream width bounded index).get second = false then second
        else Window.Enable.outputBit.flip second)
    by_cases zero : ∀ index, (Window.Enable.digitBit stream width bounded index).get first = false
    · rw [if_pos zero, if_pos (matched.mp zero)]
      exact same
    · rw [if_neg zero, if_neg (fun witness => zero (matched.mpr witness))]
      exact frontier_enable_flip first second same
  have flag : Window.Enable.outputBit.get (Window.Enable.step stream width bounded first) =
      Window.Enable.outputBit.get (Window.Enable.step stream width bounded second) :=
    output_frontier _ _ enabled
  change frontier (if Window.Enable.outputBit.get
      (Window.Enable.step stream width bounded first) then
        Window.normalBit.flip (Window.Enable.step stream width bounded first)
      else Window.Enable.step stream width bounded first) =
    frontier (if Window.Enable.outputBit.get
      (Window.Enable.step stream width bounded second) then
        Window.normalBit.flip (Window.Enable.step stream width bounded second)
      else Window.Enable.step stream width bounded second)
  rw [flag]
  cases Window.Enable.outputBit.get (Window.Enable.step stream width bounded second)
  · exact enabled
  · exact frontier_normal_flip _ _ enabled

private lemma transport_frontier_of_sourceAt {width : Nat} (same : width = 256)
    (first : ControlledResidentFrame.Data width) (second : Frame.Raw)
    (pool : first.1.1.2 = (Boundary.sourceAt same second).1.1.2)
    (flags : first.2 = (Boundary.sourceAt same second).2) :
    (Inversion.Transport.state same first).1.1.2 = second.1.1.2 ∧
      (Inversion.Transport.state same first).2 = second.2 := by
  cases same
  exact ⟨pool, flags⟩

private lemma transport_work1_of_sourceAt {width : Nat} (same : width = 256)
    (first : ControlledResidentFrame.Data width) (second : Frame.Raw)
    (value : WorkspaceReuse.largeWord first.1 =
      WorkspaceReuse.largeWord (Boundary.sourceAt same second).1) :
    Frame.work1 (Inversion.Transport.state same first) = Frame.work1 second := by
  cases same
  exact value

private lemma transport_reset {width : Nat} (same : width = 256)
    (state : ControlledResidentFrame.Data width) (reset : state.1.2 = 0) :
    Frame.numerator (Inversion.Transport.state same state) = Horner.zeroWord := by
  cases same
  exact reset


attribute [local irreducible] modulus Native.ket Window.ket Inversion.result

lemma division_afterForward_numerator (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    Frame.numerator (activeDivisionAfterForward stream width widthBound input positive bounded
      numerator flags address).1 = Fin.cast
        (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator :=
  (restore_word .numerator stream width widthBound
    (clearedResult input positive bounded numerator flags address)).trans
      (Inversion.result_numerator input positive bounded numerator (0, (0, false)) flags)

private lemma division_candidate_clean (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    Frame.CleanPool (activeDivisionClearedReset stream width widthBound input positive bounded
      numerator flags address).1 := by
  have prepared := prepare_restore stream width widthBound
    (clearedResult input positive bounded numerator flags address)
  have before : Frame.CleanPool (Control.prepareStep stream width widthBound
      (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address)).1 :=
    (congrArg (fun state : Window.Raw => state.1.1.1.2) prepared).trans
      (Inversion.result_clean_pool input positive bounded numerator (0, (0, false)) flags
        rfl rfl rfl)
  exact prepare_afterReset_cleanPool .enable stream width widthBound _
    (activeDivisionAfterForward_flags stream width widthBound input positive bounded
      numerator flags address) before

/-- Full pool, C/N/W and address agree with the actual pre-adjoint reset boundary. -/
lemma division_afterBackward_frontier (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    frontier (activeDivisionAfterBackward stream width widthBound input positive bounded
      numerator flags address) =
      frontier (afterReset .enable (activeDivisionAfterForward stream width widthBound input
        positive bounded numerator flags address)) := by
  let candidate := activeDivisionClearedReset stream width widthBound input positive bounded
    numerator flags address
  let original := ControlledResidentReuse.initial modulus input (Boundary.savedWord candidate.1)
    (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2
  have retained := transport_frontier_of_sourceAt Inversion.modulus_size original candidate.1
    (reusedInitial_pool modulus input (Boundary.savedWord candidate.1)
      (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2)
    (reusedInitial_flags modulus input (Boundary.savedWord candidate.1)
      (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2)
  have same : frontier (Inversion.Transport.state Inversion.modulus_size original, candidate.2) =
      frontier candidate := Prod.ext retained.1 (Prod.ext retained.2 rfl)
  exact (restore_frontier_congr stream width widthBound _ candidate same).trans
    (congrArg frontier (restore_prepare stream width widthBound
      (afterReset .enable (activeDivisionAfterForward stream width widthBound input positive
        bounded numerator flags address))))

/-- The phase's actual reset target is zero and its original denominator is restored. -/
lemma division_afterBackward_words (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    Frame.work2 (activeDivisionAfterBackward stream width widthBound input positive bounded
      numerator flags address).1 = Fin.cast
        (congrArg (fun size => 2 ^ size) Inversion.modulus_size) input ∧
    Frame.numerator (activeDivisionAfterBackward stream width widthBound input positive bounded
      numerator flags address).1 = Horner.zeroWord ∧
    Frame.work1 (activeDivisionAfterBackward stream width widthBound input positive bounded
      numerator flags address).1 =
      Frame.work1 (activeDivisionClearedReset stream width widthBound input positive bounded
        numerator flags address).1 := by
  let candidate := activeDivisionClearedReset stream width widthBound input positive bounded
    numerator flags address
  let original := ControlledResidentReuse.initial modulus input (Boundary.savedWord candidate.1)
    (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2
  have value : Frame.work2 (Inversion.Transport.state Inversion.modulus_size original) =
      Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) input :=
    (Inversion.Transport.state_value Inversion.modulus_size original).trans
      (congrArg (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size))
        (reusedInitial_work2 modulus input (Boundary.savedWord candidate.1)
          (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2))
  have reset := transport_reset Inversion.modulus_size original
    (reusedInitial_numerator modulus input (Boundary.savedWord candidate.1)
      (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2)
  have saved : WorkspaceReuse.largeWord original.1 =
      WorkspaceReuse.largeWord (Boundary.source candidate.1).1 := by
    have actual := reusedInitial_work1 modulus input (Boundary.savedWord candidate.1)
      (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2
    change WorkspaceReuse.largeWord original.1 =
      WorkspaceReuse.reverseWord (Boundary.savedWord candidate.1) at actual
    exact actual.trans (WorkspaceReuse.reverseWord_reverseWord _)
  have savedPhysical := transport_work1_of_sourceAt Inversion.modulus_size original candidate.1
    saved
  exact ⟨(restore_word .work2 stream width widthBound _).trans value,
    (restore_word .numerator stream width widthBound _).trans reset,
    (restore_word .work1 stream width widthBound _).trans savedPhysical⟩

private lemma division_afterBackward_flags (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    ((Placement.layout phasePorts).grouping
      (activeDivisionAfterBackward stream width widthBound input positive bounded
        numerator flags address).1).1.1.2 = false ∧
    ((Placement.layout phasePorts).grouping
      (activeDivisionAfterBackward stream width widthBound input positive bounded
        numerator flags address).1).1.2.1 = false ∧
    ((Placement.layout phasePorts).grouping
      (activeDivisionAfterBackward stream width widthBound input positive bounded
        numerator flags address).1).1.2.2 = false := by
  let candidate := activeDivisionClearedReset stream width widthBound input positive bounded
    numerator flags address
  let original := ControlledResidentReuse.initial modulus input (Boundary.savedWord candidate.1)
    (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2
  have pool : original.1.1.2 = (0, (0, false)) :=
    (reusedInitial_pool modulus input (Boundary.savedWord candidate.1)
      (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2).trans
        (sourceAt_clean Inversion.modulus_size candidate.1
          (division_candidate_clean stream width widthBound input positive bounded
            numerator flags address))
  exact restore_arithmeticFlags stream width widthBound phasePorts
    (Inversion.Transport.state Inversion.modulus_size original, candidate.2)
    (Inversion.transport_clean_pool Inversion.modulus_size original pool)

private lemma phase_coefficient_of_words (state : Window.Raw)
    (original inverse numerator : Word)
    (source : phasePorts.source.value state.1 = original)
    (saved : phasePorts.multiplier.value state.1 = Save.savedWord inverse numerator true)
    (enabled : (Phase.physicalSelector .enable).get state.1 = true)
    (cancel : Save.savedWord original (Save.savedWord inverse numerator true) true = numerator) :
    Save.savedWord (phasePorts.source.value state.1) (phasePorts.multiplier.value state.1)
        ((Phase.physicalSelector .enable).get state.1) = numerator := by
  rw [source, saved, enabled]
  exact cancel

attribute [local irreducible] activeDivisionAfterForward activeDivisionAfterBackward

private lemma division_phase_coefficient (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (canonical : numerator.val < modulus)
    (flags : Frame.Controls) (address : Window.Address)
    (enabled : (Phase.physicalSelector .enable).get
      (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address).1 = true) :
    Save.savedWord
      (phasePorts.source.value (activeDivisionAfterBackward stream width widthBound input positive
        bounded numerator flags address).1)
      (phasePorts.multiplier.value (activeDivisionAfterBackward stream width widthBound input
        positive bounded numerator flags address).1)
      ((Phase.physicalSelector .enable).get
        (activeDivisionAfterBackward stream width widthBound input positive bounded numerator
          flags address).1) =
      Frame.numerator (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address).1 := by
  let before := activeDivisionAfterForward stream width widthBound input positive bounded
    numerator flags address
  let after := activeDivisionAfterBackward stream width widthBound input positive bounded
    numerator flags address
  have words := division_afterBackward_words stream width widthBound input positive bounded
    numerator flags address
  have currentEnable : (Phase.physicalSelector .enable).get after.1 = true :=
    (enable_eq_of_pool after (afterReset .enable before)
      (congrArg Prod.fst (division_afterBackward_frontier stream width widthBound input positive
        bounded numerator flags address))).trans
      ((afterReset_selector .enable .enable before
        (activeDivisionAfterForward_flags stream width widthBound input positive bounded numerator
          flags address)).trans enabled)
  have originalY := division_afterForward_numerator stream width widthBound input positive bounded
    numerator flags address
  have saved : phasePorts.multiplier.value after.1 =
      Save.savedWord (inverseWord input positive bounded)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator) true := by
    have actual := words.2.2.trans
      ((prepare_word .work1 stream width widthBound (afterReset .enable before)).trans
        (afterReset_work1_value .enable before))
    change Frame.work1 after.1 = Save.savedWord (Frame.work2 before.1)
      (Frame.numerator before.1) ((Phase.physicalSelector .enable).get before.1) at actual
    have source := division_afterForward_work2 stream width widthBound input positive bounded
      numerator flags address
    change Frame.work2 before.1 = inverseWord input positive bounded at source
    rw [source, originalY, enabled] at actual
    exact actual
  have cancellation := savedWord_cancel
    (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) input)
    (inverseWord input positive bounded)
    (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator) true
    (fun _ => inverseWord_product input coprime positive bounded) (fun _ => canonical)
  have source : phasePorts.source.value after.1 =
      Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) input := words.1
  have coefficient := phase_coefficient_of_words after _ _ _ source saved currentEnable cancellation
  exact coefficient.trans originalY.symm

private lemma division_phaseTail_active (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (canonical : numerator.val < modulus)
    (flags : Frame.Controls) (address : Window.Address)
    (enabled : (Phase.physicalSelector .enable).get
      (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address).1 = true) (outcome : Word) :
    ((Window.suffixProgram (Phase.program phasePorts .enable outcome)).seq Swap.program).applyVec
        environment (Window.ket (activeDivisionAfterBackward stream width widthBound input positive
          bounded numerator flags address)).vec =
      WalshHadamard.walshSign outcome
        (Frame.numerator (activeDivisionAfterForward stream width widthBound input positive bounded
          numerator flags address).1) •
        (Window.ket (Swap.step (activeDivisionAfterBackward stream width widthBound input positive
          bounded numerator flags address))).vec := by
  let after := activeDivisionAfterBackward stream width widthBound input positive bounded
    numerator flags address
  have words := division_afterBackward_words stream width widthBound input positive bounded
    numerator flags address
  have phase := phaseThenSwap_applyVec .enable environment after outcome words.2.1
    (division_afterBackward_flags stream width widthBound input positive bounded numerator flags
      address) (fun _ => by
        change Canonical (Frame.work2 after.1)
        rw [words.1]
        exact bounded)
  rw [division_phase_coefficient stream width widthBound input coprime positive bounded numerator
    canonical flags address enabled] at phase
  exact phase

/-- Actual same-mask field recomputation cancels precisely the original pre-H Y character. -/
lemma divisionTail_active (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (canonical : numerator.val < modulus)
    (flags : Frame.Controls) (selected : flags.2.1 = true) (address : Window.Address)
    (enabled : (Phase.physicalSelector .enable).get
      (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address).1 = true) (outcome : Word) :
    (divisionTail stream width widthBound outcome).applyVec environment
        (Window.ket (afterReset .enable (activeDivisionAfterForward stream width widthBound input
          positive bounded numerator flags address))).vec =
      WalshHadamard.walshSign outcome
        (Frame.numerator (activeDivisionAfterForward stream width widthBound input positive bounded
          numerator flags address).1) •
        (Window.ket (Swap.step (activeDivisionAfterBackward stream width widthBound input positive
          bounded numerator flags address))).vec := by
  let before := activeDivisionAfterForward stream width widthBound input positive bounded
    numerator flags address
  let after := activeDivisionAfterBackward stream width widthBound input positive bounded
    numerator flags address
  have actualResident := normalized_action_vec
    (residentWithTemporary stream width widthBound Boundary.reusedBackward) environment
    (Window.ket (afterReset .enable before)) (Window.ket after)
    (division_savedReset_backward stream width widthBound environment input coprime positive bounded
      numerator flags selected address)
  dsimp only [divisionTail]
  rw [UnitaryCircuit.applyVec_seq, actualResident]
  exact division_phaseTail_active stream width widthBound environment input coprime positive bounded
    numerator canonical flags address enabled outcome

/-- The same actual active division record has precisely the inactive call's coefficient. -/
lemma division_branchOperator_active_ket
    {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (distinct : Function.Injective fun index => (output index).key)
    (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (store : Store ctx)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (canonical : numerator.val < modulus)
    (flags : Frame.Controls) (selected : flags.2.1 = true) (address : Window.Address)
    (enabled : (Phase.physicalSelector .enable).get
      (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address).1 = true)
    (outcome : Word) {Reference : Register} (reference : Reference.Index) :
    (branchOperator (services := services) sameWires output mask .division stream width widthBound
      store (Reset.outcomePath (services := services) .numerator sameWires output outcome
        (afterSave .enable (activeDivisionAfterForward stream width widthBound input positive
          bounded numerator flags address))) environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (activeDivisionInitial stream width widthBound input numerator flags address),
            reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (Swap.step (activeDivisionAfterBackward stream width widthBound input positive bounded
            numerator flags address)), reference)).vec := by
  have actualPrefix := divisionBeforeReset_active stream width widthBound environment input
    numerator coprime positive bounded flags selected address
  have actualTail := divisionTail_active stream width widthBound environment input coprime positive
    bounded numerator canonical flags selected address enabled outcome
  have originalY : Frame.numerator
      (afterSave .enable (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address)).1 =
      Frame.numerator (activeDivisionAfterForward stream width widthBound input positive bounded
        numerator flags address).1 :=
    Save.savedState_multiplier Save.ports .enable _
  apply call_branchOperator_corrected_ket sameWires output mask .division stream width widthBound
    distinct store outcome _ _ _ environment reference actualPrefix
  rw [originalY]
  exact actualTail

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
