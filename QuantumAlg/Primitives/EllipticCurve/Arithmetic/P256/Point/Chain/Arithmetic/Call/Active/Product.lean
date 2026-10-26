/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Active.Tail
import all
  QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Active.Result

/-!
# The actual multiplication call retains one measured-mask character

Save precedes inversion of the original denominator. The same actual reused
forward supplies inverse X for the paid same-mask phase. Its own adjoint
then restores the whole initialized source, and the real numerical swap
returns the saved product to Y. The true N selector is retained throughout.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call

noncomputable section

open MAU.Inversion.SharedEEA.Scanned
open Execution EncodedBit.WindowLookup NormalizedVector

attribute [local irreducible] modulus Inversion.initial

private lemma multiplication_candidate_clean (stream : Fin 2) (width : Nat)
    (widthBound : width ≤ 15) (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    Frame.CleanPool (activeMultiplicationClearedReset stream width widthBound input numerator
      flags address).1 := by
  let original := activeMultiplicationInitial stream width widthBound input numerator flags address
  have restored := Window.Enable.step_step stream width widthBound
    (clearedInitial input numerator flags address)
  have before : Frame.CleanPool (Window.Enable.step stream width widthBound original).1 :=
    (congrArg (fun state : Window.Raw => state.1.1.1.2) restored).trans
      (initial_clean_pool input numerator flags)
  exact enable_afterReset_cleanPool .normal stream width widthBound original
    (activeMultiplicationInitial_flags stream width widthBound input numerator flags address)
    before

private lemma multiplication_initial_normal (stream : Fin 2) (width : Nat)
    (widthBound : width ≤ 15) (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    Window.normalBit.get
        (activeMultiplicationInitial stream width widthBound input numerator flags address) =
      flags.2.1 := by
  have initialFlags : (clearedInitial input numerator flags address).1.2 = flags :=
    (congrArg (fun state : Frame.Raw => state.2)
      (initial_physical_label input numerator flags)).trans
      ((Inversion.Transport.state_flags Inversion.modulus_size
        (ControlledResident.initial modulus input numerator (0, (0, false)) flags)).trans
          (ControlledResident.initial_flags modulus input numerator (0, (0, false)) flags))
  exact (clear_normal stream width widthBound
    (clearedInitial input numerator flags address)).trans
      (congrArg (fun values : Frame.Controls => values.2.1) initialFlags)

private lemma multiplication_candidate_normal (stream : Fin 2) (width : Nat)
    (widthBound : width ≤ 15) (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (selected : flags.2.1 = true) (address : Window.Address) :
    Window.normalBit.get
      (activeMultiplicationClearedReset stream width widthBound input numerator flags address) =
        true :=
  (clear_normal stream width widthBound (afterReset .normal
    (activeMultiplicationInitial stream width widthBound input numerator flags address))).trans
      ((afterReset_selector .normal .normal _
        (activeMultiplicationInitial_flags stream width widthBound input numerator flags
          address)).trans
          ((multiplication_initial_normal stream width widthBound input numerator flags
            address).trans selected))

private lemma multiplication_candidate_initial (stream : Fin 2) (width : Nat)
    (widthBound : width ≤ 15) (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    (activeMultiplicationClearedReset stream width widthBound input numerator flags address).1 =
      Inversion.Transport.state Inversion.modulus_size
        (ControlledResidentReuse.initial modulus input
          (Boundary.savedWord
            (activeMultiplicationClearedReset stream width widthBound input numerator
              flags address).1)
          (Boundary.source
            (activeMultiplicationClearedReset stream width widthBound input numerator
              flags address).1).1.1.2
          (Boundary.source
            (activeMultiplicationClearedReset stream width widthBound input numerator
              flags address).1).2) := by
  let original := activeMultiplicationInitial stream width widthBound input numerator flags address
  have reset : Frame.numerator
      (activeMultiplicationClearedReset stream width widthBound input numerator flags address).1 =
        Horner.zeroWord :=
    (enable_numerator stream width widthBound (afterReset .normal original)).trans
      (afterReset_numerator .normal original)
  exact Boundary.source_initial input _
    (multiplication_savedReset_retained stream width widthBound input numerator flags address)
    (sourceAt_reset (width := modulus.size) Inversion.modulus_size _ reset)

private lemma swap_window_vec (environment : OracleModel.empty.Interpretation)
    (state : Window.Raw) :
    Swap.program.applyVec environment (Window.ket state).vec =
      (Window.ket (Swap.step state)).vec := by
  have initialKet : Swap.ket state = Window.ket state := rfl
  have finalKet : Swap.ket (Swap.step state) = Window.ket (Swap.step state) := rfl
  have actual := (congrArg (Swap.program.applyNormalized environment) initialKet).symm.trans
    ((Swap.program_apply environment state).trans finalKet)
  exact normalized_action_vec Swap.program environment _ _ actual

attribute [local irreducible] Native.ket Window.ket

/-- The actual multiplication forward is reversed on every original source field. -/
lemma multiplication_savedForward_backward (stream : Fin 2) (width : Nat)
    (widthBound : width ≤ 15) (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (selected : flags.2.1 = true) (address : Window.Address) :
    (residentWithNormal stream width widthBound Boundary.reusedBackward).applyNormalized environment
        (Window.ket (activeMultiplicationAfterForward stream width widthBound input positive
          bounded numerator flags address)) =
      Window.ket (afterReset .normal
        (activeMultiplicationInitial stream width widthBound input numerator flags address)) := by
  let original := activeMultiplicationInitial stream width widthBound input numerator flags address
  let candidate := activeMultiplicationClearedReset stream width widthBound input numerator
    flags address
  let result := ControlledResidentReuse.result modulus input positive bounded
    (Boundary.savedWord candidate.1) (Boundary.source candidate.1).1.1.2
    (Boundary.source candidate.1).2
  let initial := ControlledResidentReuse.initial modulus input (Boundary.savedWord candidate.1)
    (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2
  have pool := sourceAt_clean (width := modulus.size) Inversion.modulus_size candidate.1
    (multiplication_candidate_clean stream width widthBound input numerator flags address)
  have normal := sourceAt_normal (width := modulus.size) Inversion.modulus_size candidate.1
    (multiplication_candidate_normal stream width widthBound input numerator flags selected address)
  have actual := ControlledResidentReuse.backward_result modulus Inversion.modulus_nontrivial
    environment input (Boundary.savedWord candidate.1) coprime positive bounded
    (Boundary.source candidate.1).1.1.2 (congrArg Prod.fst pool)
    (congrArg (fun value => value.2.1) pool) (congrArg (fun value => value.2.2) pool)
    (Boundary.source candidate.1).2 normal
  have placed := Inversion.Transport.program_apply Inversion.modulus_size _ environment
    result initial actual
  have native : Boundary.reusedBackward.applyNormalized environment
      (Native.ket (Inversion.Transport.state Inversion.modulus_size result)) =
        Native.ket (Inversion.Transport.state Inversion.modulus_size initial) := placed
  have cleared : Window.Enable.step stream width widthBound
      (activeMultiplicationAfterForward stream width widthBound input positive bounded
        numerator flags address) =
        (Inversion.Transport.state Inversion.modulus_size result, candidate.2) :=
    Window.Enable.step_step stream width widthBound
      (Inversion.Transport.state Inversion.modulus_size result, candidate.2)
  have inputKet := congrArg (fun state : Window.Raw =>
    Boundary.reusedBackward.applyNormalized environment (Native.ket state.1)) cleared
  have transported := residentWithNormal_apply stream width widthBound Boundary.reusedBackward
    environment _ _ (inputKet.trans native)
  have initialized := multiplication_candidate_initial stream width widthBound input numerator
    flags address
  have clearedAddress := congrArg (fun state : Window.Raw => state.2) cleared
  have outputPair : (Inversion.Transport.state Inversion.modulus_size initial,
      (Window.Enable.step stream width widthBound
        (activeMultiplicationAfterForward stream width widthBound input positive bounded
          numerator flags address)).2) = candidate := by
    apply Prod.ext
    · exact initialized.symm
    · exact clearedAddress
  have outputState : Window.Enable.step stream width widthBound
      (Inversion.Transport.state Inversion.modulus_size initial,
        (Window.Enable.step stream width widthBound
          (activeMultiplicationAfterForward stream width widthBound input positive bounded
            numerator flags address)).2) = afterReset .normal original :=
    (congrArg (Window.Enable.step stream width widthBound) outputPair).trans
      (Window.Enable.step_step stream width widthBound (afterReset .normal original))
  exact transported.trans (congrArg Window.ket outputState)

/-- All numerical phase operands are read from the actual reused-forward output. -/
lemma multiplication_afterForward_words (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    Frame.work2 (activeMultiplicationAfterForward stream width widthBound input positive bounded
      numerator flags address).1 = inverseWord input positive bounded ∧
    Frame.numerator (activeMultiplicationAfterForward stream width widthBound input positive bounded
      numerator flags address).1 = Horner.zeroWord ∧
    Frame.work1 (activeMultiplicationAfterForward stream width widthBound input positive bounded
      numerator flags address).1 =
      Frame.work1 (activeMultiplicationClearedReset stream width widthBound input numerator
        flags address).1 := by
  let candidate := activeMultiplicationClearedReset stream width widthBound input numerator
    flags address
  let result := ControlledResidentReuse.result modulus input positive bounded
    (Boundary.savedWord candidate.1) (Boundary.source candidate.1).1.1.2
    (Boundary.source candidate.1).2
  have value : Frame.work2 (Inversion.Transport.state Inversion.modulus_size result) =
      inverseWord input positive bounded :=
    (Inversion.Transport.state_value Inversion.modulus_size result).trans
      (congrArg (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size))
        (reusedResult_work2 modulus input positive bounded (Boundary.savedWord candidate.1)
          (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2))
  have reset := transport_reset Inversion.modulus_size result
    (reusedResult_numerator modulus input coprime positive bounded (Boundary.savedWord candidate.1)
      (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2)
  have saved : WorkspaceReuse.largeWord result.1 =
      WorkspaceReuse.largeWord (Boundary.source candidate.1).1 := by
    have actual := reusedResult_work1 modulus input positive bounded
      (Boundary.savedWord candidate.1)
      (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2
    change WorkspaceReuse.largeWord result.1 =
      WorkspaceReuse.reverseWord (Boundary.savedWord candidate.1) at actual
    exact actual.trans (WorkspaceReuse.reverseWord_reverseWord _)
  have savedPhysical := transport_work1_of_sourceAt Inversion.modulus_size result candidate.1 saved
  exact ⟨(enable_word .work2 stream width widthBound _).trans value,
    (enable_word .numerator stream width widthBound _).trans reset,
    (enable_word .work1 stream width widthBound _).trans savedPhysical⟩

private lemma multiplication_afterForward_normal (stream : Fin 2) (width : Nat)
    (widthBound : width ≤ 15) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (selected : flags.2.1 = true) (address : Window.Address) :
    (Phase.physicalSelector .normal).get
      (activeMultiplicationAfterForward stream width widthBound input positive bounded
        numerator flags address).1 = true := by
  let candidate := activeMultiplicationClearedReset stream width widthBound input numerator
    flags address
  let result := ControlledResidentReuse.result modulus input positive bounded
    (Boundary.savedWord candidate.1) (Boundary.source candidate.1).1.1.2
    (Boundary.source candidate.1).2
  have flagsRead := (Inversion.Transport.state_flags Inversion.modulus_size result).trans
    (reusedResult_flags modulus input positive bounded (Boundary.savedWord candidate.1)
      (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2)
  have normal := sourceAt_normal (width := modulus.size) Inversion.modulus_size candidate.1
    (multiplication_candidate_normal stream width widthBound input numerator flags selected address)
  exact (clear_normal stream width widthBound
    (Inversion.Transport.state Inversion.modulus_size result, candidate.2)).trans
      ((congrArg (fun values : Frame.Controls => values.2.1) flagsRead).trans normal)

private lemma multiplication_afterForward_flags (stream : Fin 2) (width : Nat)
    (widthBound : width ≤ 15) (input : Fin (2 ^ modulus.size))
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    ((Placement.layout phasePorts).grouping
      (activeMultiplicationAfterForward stream width widthBound input positive bounded
        numerator flags address).1).1.1.2 = false ∧
    ((Placement.layout phasePorts).grouping
      (activeMultiplicationAfterForward stream width widthBound input positive bounded
        numerator flags address).1).1.2.1 = false ∧
    ((Placement.layout phasePorts).grouping
      (activeMultiplicationAfterForward stream width widthBound input positive bounded
        numerator flags address).1).1.2.2 = false := by
  let candidate := activeMultiplicationClearedReset stream width widthBound input numerator
    flags address
  let result := ControlledResidentReuse.result modulus input positive bounded
    (Boundary.savedWord candidate.1) (Boundary.source candidate.1).1.1.2
    (Boundary.source candidate.1).2
  have pool := (reusedResult_pool modulus input positive bounded (Boundary.savedWord candidate.1)
    (Boundary.source candidate.1).1.1.2 (Boundary.source candidate.1).2).trans
      (sourceAt_clean (width := modulus.size) Inversion.modulus_size candidate.1
        (multiplication_candidate_clean stream width widthBound input numerator flags address))
  exact enable_arithmeticFlags stream width widthBound phasePorts
    (Inversion.Transport.state Inversion.modulus_size result, candidate.2)
    (Inversion.transport_clean_pool Inversion.modulus_size result pool)

lemma multiplication_initial_numerator (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address) :
    Frame.numerator (activeMultiplicationInitial stream width widthBound input numerator
      flags address).1 = Fin.cast
        (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator := by
  have initial := congrArg Frame.numerator (initial_physical_label input numerator flags)
  have transported := (Inversion.Transport.state_numerator Inversion.modulus_size
    (ControlledResident.initial modulus input numerator (0, (0, false)) flags)).trans
      (congrArg (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size))
        (ControlledResident.initial_numerator modulus input numerator (0, (0, false)) flags))
  exact (enable_word .numerator stream width widthBound
    (clearedInitial input numerator flags address)).trans (initial.trans transported)

private lemma multiplication_initial_work2 (stream : Fin 2) (width : Nat)
    (widthBound : width ≤ 15) (input numerator : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    Frame.work2 (activeMultiplicationInitial stream width widthBound input numerator
      flags address).1 = Fin.cast
        (congrArg (fun size => 2 ^ size) Inversion.modulus_size) input :=
  (enable_word .work2 stream width widthBound
    (clearedInitial input numerator flags address)).trans
      (Inversion.initial_value input numerator (0, (0, false)) flags)

private lemma normal_phase_coefficient_of_words (state : Window.Raw)
    (first second numerator : Word)
    (source : phasePorts.source.value state.1 = first)
    (saved : phasePorts.multiplier.value state.1 = Save.savedWord second numerator true)
    (enabled : (Phase.physicalSelector .normal).get state.1 = true)
    (cancel : Save.savedWord first (Save.savedWord second numerator true) true = numerator) :
    Save.savedWord (phasePorts.source.value state.1) (phasePorts.multiplier.value state.1)
        ((Phase.physicalSelector .normal).get state.1) = numerator := by
  rw [source, saved, enabled]
  exact cancel

attribute [local irreducible] activeMultiplicationInitial activeMultiplicationAfterForward

private lemma multiplication_phase_coefficient (stream : Fin 2) (width : Nat)
    (widthBound : width ≤ 15)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (canonical : numerator.val < modulus)
    (flags : Frame.Controls) (selected : flags.2.1 = true) (address : Window.Address) :
    Save.savedWord
      (phasePorts.source.value (activeMultiplicationAfterForward stream width widthBound input
        positive bounded numerator flags address).1)
      (phasePorts.multiplier.value (activeMultiplicationAfterForward stream width widthBound input
        positive bounded numerator flags address).1)
      ((Phase.physicalSelector .normal).get
        (activeMultiplicationAfterForward stream width widthBound input positive bounded numerator
          flags address).1) =
      Frame.numerator (activeMultiplicationInitial stream width widthBound input numerator
        flags address).1 := by
  let original := activeMultiplicationInitial stream width widthBound input numerator flags address
  let after := activeMultiplicationAfterForward stream width widthBound input positive bounded
    numerator flags address
  have words := multiplication_afterForward_words stream width widthBound input coprime positive
    bounded numerator flags address
  have normal := multiplication_afterForward_normal stream width widthBound input positive bounded
    numerator flags selected address
  have originalNormal : (Phase.physicalSelector .normal).get original.1 = true :=
    (multiplication_initial_normal stream width widthBound input numerator flags address).trans
      selected
  have originalX := multiplication_initial_work2 stream width widthBound input numerator flags
    address
  have originalY := multiplication_initial_numerator stream width widthBound input numerator flags
    address
  have saved : phasePorts.multiplier.value after.1 =
      Save.savedWord (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) input)
        (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator) true := by
    have actual := words.2.2.trans
      ((enable_word .work1 stream width widthBound (afterReset .normal original)).trans
        (afterReset_work1_value .normal original))
    change Frame.work1 after.1 = Save.savedWord (Frame.work2 original.1)
      (Frame.numerator original.1) ((Phase.physicalSelector .normal).get original.1) at actual
    rw [originalX, originalY, originalNormal] at actual
    exact actual
  have cancellation := savedWord_cancel (inverseWord input positive bounded)
    (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) input)
    (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size) numerator) true
    (fun _ => by
      change Nat.ModEq modulus ((inverseWord input positive bounded).val * input.val) 1
      rw [Nat.mul_comm]
      exact inverseWord_product input coprime positive bounded)
    (fun _ => canonical)
  have source : phasePorts.source.value after.1 = inverseWord input positive bounded := words.1
  have coefficient := normal_phase_coefficient_of_words after _ _ _ source saved normal cancellation
  exact coefficient.trans originalY.symm

private lemma multiplication_phase_active (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (canonical : numerator.val < modulus)
    (flags : Frame.Controls) (selected : flags.2.1 = true) (address : Window.Address)
    (outcome : Word) :
    (Window.suffixProgram (Phase.program phasePorts .normal outcome)).applyVec environment
        (Window.ket (activeMultiplicationAfterForward stream width widthBound input positive bounded
          numerator flags address)).vec =
      WalshHadamard.walshSign outcome
        (Frame.numerator (activeMultiplicationInitial stream width widthBound input numerator
          flags address).1) •
        (Window.ket (activeMultiplicationAfterForward stream width widthBound input positive bounded
          numerator flags address)).vec := by
  let after := activeMultiplicationAfterForward stream width widthBound input positive bounded
    numerator flags address
  have words := multiplication_afterForward_words stream width widthBound input coprime positive
    bounded numerator flags address
  have phase := suffixPhase_applyVec_of_flags .normal environment after outcome words.2.1
    (multiplication_afterForward_flags stream width widthBound input positive bounded numerator
      flags address) (fun _ => by
        change Canonical (Frame.work2 after.1)
        rw [words.1]
        exact inverseWord_canonical input coprime positive bounded)
  rw [multiplication_phase_coefficient stream width widthBound input coprime positive bounded
    numerator canonical flags selected address] at phase
  exact phase

/-- The real inverse-X recomputation cancels the same pre-H numerator character. -/
lemma multiplicationTail_active (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation)
    (input : Fin (2 ^ modulus.size)) (coprime : Nat.Coprime input.val modulus)
    (positive : 0 < input.val) (bounded : input.val < modulus)
    (numerator : Fin (2 ^ modulus.size)) (canonical : numerator.val < modulus)
    (flags : Frame.Controls) (selected : flags.2.1 = true) (address : Window.Address)
    (outcome : Word) :
    (multiplicationTail stream width widthBound outcome).applyVec environment
        (Window.ket (afterReset .normal
          (activeMultiplicationInitial stream width widthBound input numerator flags
            address))).vec =
      WalshHadamard.walshSign outcome
        (Frame.numerator (activeMultiplicationInitial stream width widthBound input numerator
          flags address).1) •
        (Window.ket (Swap.step (afterReset .normal
          (activeMultiplicationInitial stream width widthBound input numerator flags
            address)))).vec := by
  let original := activeMultiplicationInitial stream width widthBound input numerator flags address
  let after := activeMultiplicationAfterForward stream width widthBound input positive bounded
    numerator flags address
  have phase := multiplication_phase_active stream width widthBound environment input coprime
    positive bounded numerator canonical flags selected address outcome
  have forward := normalized_action_vec
    (residentWithNormal stream width widthBound Boundary.reusedForward) environment
    (Window.ket (afterReset .normal original)) (Window.ket after)
    (multiplication_savedReset_forward stream width widthBound environment input coprime positive
      bounded numerator flags selected address)
  have backward := normalized_action_vec
    (residentWithNormal stream width widthBound Boundary.reusedBackward) environment
    (Window.ket after) (Window.ket (afterReset .normal original))
    (multiplication_savedForward_backward stream width widthBound environment input coprime positive
      bounded numerator flags selected address)
  dsimp only [multiplicationTail]
  rw [UnitaryCircuit.applyVec_seq, forward, UnitaryCircuit.applyVec_seq, phase,
    UnitaryCircuit.applyVec_smul, UnitaryCircuit.applyVec_seq, backward,
    swap_window_vec environment (afterReset .normal original)]

/-- Every actual active multiplication record has the same reference-coherent coefficient. -/
lemma multiplication_branchOperator_active_ket
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
    (outcome : Word) {Reference : Register} (reference : Reference.Index) :
    (branchOperator (services := services) sameWires output mask .multiplication stream width
      widthBound store (Reset.outcomePath (services := services) .numerator sameWires output outcome
        (afterSave .normal (activeMultiplicationInitial stream width widthBound input numerator
          flags address))) environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (activeMultiplicationInitial stream width widthBound input numerator flags address),
            reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (Swap.step (afterReset .normal (activeMultiplicationInitial stream width widthBound input
            numerator flags address))), reference)).vec := by
  have actualPrefix := multiplicationBeforeReset_active stream width widthBound environment input
    numerator bounded flags address
  have actualTail := multiplicationTail_active stream width widthBound environment input coprime
    positive bounded numerator canonical flags selected address outcome
  have originalY : Frame.numerator (afterSave .normal
      (activeMultiplicationInitial stream width widthBound input numerator flags address)).1 =
      Frame.numerator
        (activeMultiplicationInitial stream width widthBound input numerator flags address).1 :=
    Save.savedState_multiplier Save.ports .normal _
  apply call_branchOperator_corrected_ket sameWires output mask .multiplication stream width
    widthBound distinct store outcome _ _ _ environment reference actualPrefix
  rw [originalY]
  exact actualTail

end

end Arithmetic.Call

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
