/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint.Prepare

/-!
# One actual division record law on the original enabled label

The caller supplies the initialized source and the original arithmetic
domain only when the complete digit is nonzero. Temporary N, clearing
the entire pool and restoring the live F are internal consequences of
the actual control transfer, rather than caller coordinate premises.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

open Execution EncodedBit.WindowLookup NormalizedVector

attribute [local irreducible] modulus Native.ket Window.ket inputState

/-- Complete selected output, or the same arbitrary original binary label when disabled. -/
def divisionOutput (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address)
    (admitted : divisionEnabled stream width bounded input numerator flags address = true →
      ActiveDomain input numerator) : Window.Raw :=
  if selected : divisionEnabled stream width bounded input numerator flags address = true then
    Swap.step (activeDivisionAfterBackward stream width bounded input
      (admitted selected).positive (admitted selected).bounded numerator
      (divisionFlags stream width bounded input numerator flags address) address)
  else inputState stream width bounded input numerator flags address

private lemma divisionOutput_selected (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    (admitted : divisionEnabled stream width bounded input numerator flags address = true →
      ActiveDomain input numerator)
    (selected : divisionEnabled stream width bounded input numerator flags address = true) :
    divisionOutput stream width bounded input numerator flags address admitted =
      Swap.step (activeDivisionAfterBackward stream width bounded input
        (admitted selected).positive (admitted selected).bounded numerator
        (divisionFlags stream width bounded input numerator flags address) address) :=
  dif_pos selected

private lemma divisionOutput_disabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (address : Window.Address)
    (admitted : divisionEnabled stream width bounded input numerator flags address = true →
      ActiveDomain input numerator)
    (selected : ¬ divisionEnabled stream width bounded input numerator flags address = true) :
    divisionOutput stream width bounded input numerator flags address admitted =
      inputState stream width bounded input numerator flags address :=
  dif_neg selected

private lemma inputState_enable (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    (Phase.physicalSelector .enable).get
        (inputState stream width bounded input numerator flags address).1 =
      divisionEnabled stream width bounded input numerator flags address := by
  have actual : (Phase.physicalSelector .enable).get
      (activeMultiplicationInitial stream width bounded input numerator flags address).1 =
        divisionEnabled stream width bounded input numerator flags address :=
    (Control.flag_get _).symm.trans
      (Window.Enable.step_output_of_zero stream width bounded _
        (Window.Enable.outputBit_clean _ (initial_clean_pool input numerator flags)))
  exact (congrArg (fun state : Window.Raw => (Phase.physicalSelector .enable).get state.1)
    (inputState_eq stream width bounded input numerator flags address)).trans actual

private lemma division_prepared_disabled (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (normalZero : flags.2.1 = false) (address : Window.Address)
    (disabled : divisionEnabled stream width bounded input numerator flags address = false) :
    Control.prepareStep stream width bounded
        (inputState stream width bounded input numerator flags address) =
      Window.Enable.step stream width bounded
        (inputState stream width bounded input numerator flags address) := by
  rw [division_prepared stream width bounded input numerator flags normalZero address,
    inputState_clear]
  have flagsSame : divisionFlags stream width bounded input numerator flags address = flags := by
    dsimp only [divisionFlags]
    rw [disabled]
    exact (congrArg (setNormal flags) normalZero).symm.trans (by rfl)
  rw [flagsSame]

private lemma divisionEnabled_setNormal (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls) (value : Bool)
    (address : Window.Address) :
    divisionEnabled stream width bounded input numerator (setNormal flags value) address =
      divisionEnabled stream width bounded input numerator flags address := by
  have reads (index : Fin (width + 1)) :
      (Window.Enable.digitBit stream width bounded index).get
          (clearedInitial input numerator (setNormal flags value) address) =
        (Window.Enable.digitBit stream width bounded index).get
          (clearedInitial input numerator flags address) := by
    refine Fin.cases ?_ (fun _ => ?_) index
    · change (Window.streamBit stream).get _ = (Window.streamBit stream).get _
      unfold Window.streamBit
      split
      · change (clearedInitial input numerator (setNormal flags value) address).1.2.1 =
          (clearedInitial input numerator flags address).1.2.1
        rw [clearedInitial_flags, clearedInitial_flags]
        rfl
      · change (clearedInitial input numerator (setNormal flags value) address).1.2.2.2 =
          (clearedInitial input numerator flags address).1.2.2.2
        rw [clearedInitial_flags, clearedInitial_flags]
        rfl
    · rfl
  have predicate :
      (∀ index, (Window.Enable.digitBit stream width bounded index).get
        (clearedInitial input numerator (setNormal flags value) address) = false) ↔
      (∀ index, (Window.Enable.digitBit stream width bounded index).get
        (clearedInitial input numerator flags address) = false) :=
    forall_congr' (fun index => by rw [reads index])
  simp only [divisionEnabled, Control.digitEnabled, predicate]

/-- The same actual record coefficient covers active and arbitrary inactive labels. -/
private lemma division_branchOperator_inactive
    {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (distinct : Function.Injective fun index => (output index).key)
    (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (store : Store ctx)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (normalZero : flags.2.1 = false) (address : Window.Address)
    (admitted : divisionEnabled stream width widthBound input numerator flags address = true →
      ActiveDomain input numerator)
    (selected : ¬ divisionEnabled stream width widthBound input numerator flags address = true)
    (outcome : Word) {Reference : Register} (reference : Reference.Index) :
    (branchOperator (services := services) sameWires output mask .division stream width widthBound
      store (Reset.outcomePath (services := services) .numerator sameWires output outcome
        (inputState stream width widthBound input numerator flags address))
      environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (inputState stream width widthBound input numerator flags address), reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (divisionOutput stream width widthBound input numerator flags address admitted),
            reference)).vec := by
  have disabledDigit : divisionEnabled stream width widthBound input numerator flags address =
      false := Bool.eq_false_iff.mpr selected
  let original := inputState stream width widthBound input numerator flags address
  have prepared := division_prepared_disabled stream width widthBound input numerator flags
    normalZero address disabledDigit
  have actual := division_branchOperator_disabled_ket (services := services) sameWires output mask
    stream width widthBound distinct store outcome original environment reference
    (inputState_work1 stream width widthBound input numerator flags address)
    (inputState_flags stream width widthBound input numerator flags address)
    ((congrArg (fun state : Window.Raw => state.1.1.1.2) prepared).trans
      (inputState_clear_clean stream width widthBound input numerator flags address))
    ((congrArg (fun state : Window.Raw => state.1.1.1.1.control) prepared).trans
      (inputState_clear_control stream width widthBound input numerator flags address))
    ((congrArg (fun state : Window.Raw => state.1.2.2.1) prepared).trans
      ((inputState_clear_normal stream width widthBound input numerator flags address).trans
        normalZero))
    ((inputState_enable stream width widthBound input numerator flags address).trans
      disabledDigit)
  rw [Reset.outcomePath_eq .numerator sameWires output outcome _ (afterSave .enable original)]
  exact actual.trans (congrArg (fun state : Window.Raw => invSqrt2 ^ 256 •
    (NormalizedVector.ket (R := Register.prod ctx.register Reference)
      (measuredEncodedBasis (QubitLayout.canonical _) sameWires state, reference)).vec)
    (divisionOutput_disabled stream width widthBound input numerator flags address admitted
      selected).symm)

lemma division_branchOperator_ket
    {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (distinct : Function.Injective fun index => (output index).key)
    (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (store : Store ctx)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (normalZero : flags.2.1 = false) (address : Window.Address)
    (admitted : divisionEnabled stream width widthBound input numerator flags address = true →
      ActiveDomain input numerator)
    (outcome : Word) {Reference : Register} (reference : Reference.Index) :
    (branchOperator (services := services) sameWires output mask .division stream width widthBound
      store (Reset.outcomePath (services := services) .numerator sameWires output outcome
        (inputState stream width widthBound input numerator flags address))
      environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (inputState stream width widthBound input numerator flags address), reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (divisionOutput stream width widthBound input numerator flags address admitted),
            reference)).vec := by
  by_cases selected : divisionEnabled stream width widthBound input numerator flags address = true
  · have domain := admitted selected
    let temporary := divisionFlags stream width widthBound input numerator flags address
    have normalSelected : temporary.2.1 = true := selected
    have enabled : (Phase.physicalSelector .enable).get
        (activeDivisionAfterForward stream width widthBound input domain.positive domain.bounded
          numerator temporary address).1 = true :=
      (division_forward_enable stream width widthBound input domain.positive domain.bounded
        numerator temporary address).trans
          ((divisionEnabled_setNormal stream width widthBound input numerator flags _ address).trans
            selected)
    have actual := division_branchOperator_active_ket (services := services) sameWires output mask
      distinct stream width widthBound environment store input domain.coprime domain.positive
      domain.bounded numerator
      domain.canonical temporary normalSelected address enabled outcome reference
    rw [Reset.outcomePath_eq .numerator sameWires output outcome _
      (afterSave .enable (activeDivisionAfterForward stream width widthBound input domain.positive
        domain.bounded numerator temporary address))]
    have sameInput := division_input_eq stream width widthBound input numerator flags normalZero
      address
    have transported := (congrArg (fun state : Window.Raw =>
      (branchOperator (services := services) sameWires output mask .division stream width widthBound
        store (Reset.outcomePath (services := services) .numerator sameWires output outcome
          (afterSave .enable (activeDivisionAfterForward stream width widthBound input
            domain.positive domain.bounded numerator temporary address)))
        environment Reference).applyVec
          (NormalizedVector.ket (R := Register.prod ctx.register Reference)
            (measuredEncodedBasis (QubitLayout.canonical _) sameWires state, reference)).vec)
      sameInput).trans actual
    have finalTransport := reference_ket_smul_congr (Physical := ctx.register)
      (Reference := Reference)
      (measuredEncodedBasis (encoding := Window.encoding) (QubitLayout.canonical _) sameWires)
      (invSqrt2 ^ 256) _ _
      (divisionOutput_selected stream width widthBound input numerator flags address admitted
        selected).symm reference
    exact transported.trans finalTransport
  · exact division_branchOperator_inactive (services := services) sameWires output mask distinct
      stream width widthBound environment store input numerator flags normalZero address admitted
      selected outcome reference

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
