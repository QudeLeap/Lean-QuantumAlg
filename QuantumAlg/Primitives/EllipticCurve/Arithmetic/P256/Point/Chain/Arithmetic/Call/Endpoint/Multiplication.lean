/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Arithmetic.Call.Endpoint

/-!
# One actual multiplication record law for both genuine N sectors

The exact operator, original Store and real reset path are common to both
sectors. The arithmetic domain is required only if genuine N is true.
When N is false, arbitrary original binary X and Y are restored, including
labels for which the live whole-digit enable F is true.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Arithmetic.Call.Endpoint

noncomputable section

open Execution EncodedBit.WindowLookup NormalizedVector

/-- The exact complete label returned by the actual save, reset, own adjoint and swap. -/
def multiplicationOutput (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) : Window.Raw :=
  Swap.step (afterReset .normal (inputState stream width bounded input numerator flags address))

lemma multiplicationOutput_step (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (address : Window.Address) :
    multiplicationOutput stream width bounded input numerator flags address =
      Swap.step (afterReset .normal (inputState stream width bounded input numerator flags
        address)) := rfl

attribute [local irreducible] modulus Native.ket Window.ket inputState multiplicationOutput

/-- Both coherent genuine-N sectors obey the same actual record law and common coefficient. -/
private lemma multiplication_branchOperator_inactive
    {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (distinct : Function.Injective fun index => (output index).key)
    (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (store : Store ctx)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (selected : flags.2.1 = false) (address : Window.Address)
    (outcome : Word) {Reference : Register} (reference : Reference.Index) :
    (branchOperator (services := services) sameWires output mask .multiplication stream width
      widthBound store (Reset.outcomePath (services := services) .numerator sameWires output outcome
        (afterSave .normal (inputState stream width widthBound input numerator flags address)))
      environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (inputState stream width widthBound input numerator flags address), reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (multiplicationOutput stream width widthBound input numerator flags address),
            reference)).vec := by
  let original := inputState stream width widthBound input numerator flags address
  have flagsZero := inputState_flags stream width widthBound input numerator flags address
  have targetZero := inputState_work1 stream width widthBound input numerator flags address
  have disabled : (Phase.physicalSelector .normal).get original.1 = false :=
    (inputState_normal stream width widthBound input numerator flags address).trans selected
  have actual := multiplication_branchOperator_disabled_ket (services := services) sameWires
    output mask stream width widthBound distinct store outcome original environment reference
    targetZero flagsZero
    (inputState_clear_clean stream width widthBound input numerator flags address)
    (inputState_clear_control stream width widthBound input numerator flags address)
    ((inputState_clear_normal stream width widthBound input numerator flags address).trans
      selected)
  have restored : multiplicationOutput stream width widthBound input numerator flags address =
      original := by
    have outputSame : multiplicationOutput stream width widthBound input numerator flags address =
        Swap.step (afterReset .normal original) :=
      multiplicationOutput_step stream width widthBound input numerator flags address
    exact outputSame.trans
      (swap_afterReset_disabled .normal original targetZero flagsZero disabled)
  exact actual.trans (congrArg (fun final : Window.Raw => invSqrt2 ^ 256 •
    (NormalizedVector.ket (R := Register.prod ctx.register Reference)
      (measuredEncodedBasis (QubitLayout.canonical _) sameWires final, reference)).vec)
    restored.symm)

lemma multiplication_branchOperator_ket
    {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (sameWires : (QubitLayout.canonical Window.encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (output : Fin 256 → CWriteRef ctx (.finite 2)) (mask : CWriteRef ctx (.bits 256))
    (distinct : Function.Injective fun index => (output index).key)
    (stream : Fin 2) (width : Nat) (widthBound : width ≤ 15)
    (environment : OracleModel.empty.Interpretation) (store : Store ctx)
    (input numerator : Fin (2 ^ modulus.size)) (flags : Frame.Controls)
    (admitted : flags.2.1 = true → ActiveDomain input numerator) (address : Window.Address)
    (outcome : Word) {Reference : Register} (reference : Reference.Index) :
    (branchOperator (services := services) sameWires output mask .multiplication stream width
      widthBound store (Reset.outcomePath (services := services) .numerator sameWires output outcome
        (afterSave .normal (inputState stream width widthBound input numerator flags address)))
      environment Reference).applyVec
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (inputState stream width widthBound input numerator flags address), reference)).vec =
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires
          (multiplicationOutput stream width widthBound input numerator flags address),
            reference)).vec := by
  cases selected : flags.2.1 with
  | true =>
    have domain := admitted selected
    have actual := multiplication_branchOperator_active_ket (services := services) sameWires output
      mask distinct stream width widthBound environment store input domain.coprime domain.positive
      domain.bounded
      numerator domain.canonical flags selected address outcome reference
    have initialSame : inputState stream width widthBound input numerator flags address =
        activeMultiplicationInitial stream width widthBound input numerator flags address :=
      inputState_eq stream width widthBound input numerator flags address
    have finalSame : multiplicationOutput stream width widthBound input numerator flags address =
        Swap.step (afterReset .normal (activeMultiplicationInitial stream width widthBound input
          numerator flags address)) :=
      (multiplicationOutput_step stream width widthBound input numerator flags address).trans
        (congrArg (fun state : Window.Raw => Swap.step (afterReset .normal state)) initialSame)
    have initialTransport := congrArg (fun state : Window.Raw =>
      (branchOperator (services := services) sameWires output mask .multiplication stream width
        widthBound store (Reset.outcomePath (services := services) .numerator sameWires output
          outcome (afterSave .normal state)) environment Reference).applyVec
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis (QubitLayout.canonical _) sameWires state, reference)).vec)
      initialSame
    exact initialTransport.trans (actual.trans (congrArg (fun state : Window.Raw =>
      invSqrt2 ^ 256 • (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis (QubitLayout.canonical _) sameWires state, reference)).vec)
      finalSame.symm))
  | false =>
    exact multiplication_branchOperator_inactive (services := services) sameWires output mask
      distinct stream width widthBound environment store input numerator flags selected address
      outcome reference

end

end Arithmetic.Call.Endpoint

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
