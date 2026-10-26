/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Stream
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Reference

/-!
# Whole arithmetic programs on either stream of the original window bank

The original arithmetic endpoint is extended by the existing address systems
and physically placed as a complete program. The generic transport is proved
before choosing the point width. Every retained original system, the other
coherent stream and all fifteen address systems remain in the complete label.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

noncomputable section

open QuantumAlg.EncodedBit
open scoped BigOperators

private lemma placed_suffix_ket {Data Extra : Type}
    (dataEncoding : BinaryLabelEncoding Data) (extraEncoding : BinaryLabelEncoding Extra)
    (placement : FullPlacement (.prod dataEncoding extraEncoding)
      (.prod dataEncoding extraEncoding))
    {gates : GateModel} {oracles : OracleModel}
    (body : UnitaryCircuit gates oracles
      (QubitLayout.canonical dataEncoding.width).toQuantum)
    (environment : oracles.Interpretation) (initial final : Data) (extra : Extra)
    (actual : body.applyNormalized environment
        (NormalizedVector.ket ((QubitLayout.canonical dataEncoding.width).basisEquiv.symm
          (dataEncoding.encode initial))) =
      NormalizedVector.ket ((QubitLayout.canonical dataEncoding.width).basisEquiv.symm
        (dataEncoding.encode final))) :
    (placement.place (UnitaryCircuit.onBinaryPrefix extraEncoding.width body)).applyNormalized
        environment (NormalizedVector.ket
          ((QubitLayout.canonical (dataEncoding.width + extraEncoding.width)).basisEquiv.symm
            ((BinaryLabelEncoding.prod dataEncoding extraEncoding).encode
              (placement.grouping.symm (initial, extra))))) =
      NormalizedVector.ket
        ((QubitLayout.canonical (dataEncoding.width + extraEncoding.width)).basisEquiv.symm
          ((BinaryLabelEncoding.prod dataEncoding extraEncoding).encode
            (placement.grouping.symm (final, extra)))) :=
  placement.place_ket_of_eq _ _ _
    (UnitaryCircuit.Realizes.onBinaryPrefix_applyNormalized_encoded_ket_of_eq
      dataEncoding extraEncoding body initial final extra actual)

def streamInput (stream : Fin 2) (state : Frame.Raw) (address : Address) : Raw :=
  (streamPlacement stream).grouping.symm (state, address)

def ket (state : Raw) :
    NormalizedVector (QubitLayout.canonical encoding.width).toQuantum.register :=
  NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm (encoding.encode state))

lemma streamInput_grouping (stream : Fin 2) (state : Frame.Raw) (address : Address) :
    (streamPlacement stream).grouping (streamInput stream state address) = (state, address) :=
  (streamPlacement stream).grouping.apply_symm_apply _

lemma streamInput_eq (stream : Fin 2) (state : Frame.Raw) (address : Address) :
    streamInput stream state address =
      if stream.val = 0 then (state, address)
      else ((state.1, (state.2.2.2, (state.2.2.1, state.2.1))), address) := by
  apply (streamPlacement stream).grouping.injective
  rw [streamInput_grouping]
  by_cases first : stream.val = 0
  · rw [if_pos first, streamPlacement_grouping, if_pos first]
  · rw [if_neg first, streamPlacement_grouping, if_neg first]

lemma streamInput_address (stream : Fin 2) (state : Frame.Raw) (address : Address) :
    (streamInput stream state address).2 = address := by
  rw [streamInput_eq]
  split <;> rfl

/-- No arithmetic AST is unfolded when transporting its actual admitted-input equation. -/
lemma program_ket_of_eq (stream : Fin 2) (body : Native.Circuit)
    (environment : OracleModel.empty.Interpretation) (initial final : Frame.Raw)
    (address : Address)
    (actual : body.applyNormalized environment (Native.ket initial) = Native.ket final) :
    (program stream body).applyNormalized environment (ket (streamInput stream initial address)) =
      ket (streamInput stream final address) :=
  placed_suffix_ket Frame.encoding addressEncoding (streamPlacement stream)
    body environment initial final address actual

lemma cleanProgram_canonical (stream : Fin 2) (ports : PortAssignment)
    (control : Native.Control) (choice : Native.Multiplier)
    (environment : OracleModel.empty.Interpretation) (source multiplier : Word)
    (canonical : Canonical source) (retained : Placement.Rest ports) (address : Address) :
    (program stream (Native.cleanProgram ports control choice)).applyNormalized environment
        (ket (streamInput stream
          (Native.arithmeticState ports source Horner.zeroWord multiplier retained) address)) =
      ket (streamInput stream (Native.arithmeticState ports source
        (Horner.productWord source
          ((Native.quantumMultiplier ports choice).value source (multiplier, retained))
          ((Native.controlBit ports control).get retained)) multiplier retained) address) :=
  program_ket_of_eq stream _ environment _ _ address
    (Native.cleanProgram_canonical ports control choice environment source multiplier
      canonical retained)

lemma macProgram_canonical (stream : Fin 2) (ports : PortAssignment) (control : Native.Control)
    (environment : OracleModel.empty.Interpretation) (source target multiplier : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (retained : Placement.Rest ports) (address : Address) :
    (program stream (Native.macProgram ports control)).applyNormalized environment
        (ket (streamInput stream
          (Native.arithmeticState ports source target multiplier retained) address)) =
      ket (streamInput stream (Native.arithmeticState ports source
        (Accumulate.accumulatedWord source multiplier target
          ((Native.controlBit ports control).get retained)) multiplier retained) address) :=
  program_ket_of_eq stream _ environment _ _ address
    (Native.macProgram_canonical ports control environment source target multiplier
      sourceCanonical targetCanonical retained)

lemma inverseMacProgram_canonical (stream : Fin 2) (ports : PortAssignment)
    (control : Native.Control) (environment : OracleModel.empty.Interpretation)
    (source target multiplier : Word) (sourceCanonical : Canonical source)
    (targetCanonical : Canonical target) (retained : Placement.Rest ports) (address : Address) :
    (program stream (Native.inverseMacProgram ports control)).applyNormalized environment
        (ket (streamInput stream
          (Native.arithmeticState ports source target multiplier retained) address)) =
      ket (streamInput stream (Native.arithmeticState ports source
        (Accumulate.Inverse.differenceWord source multiplier target
          ((Native.controlBit ports control).get retained)) multiplier retained) address) :=
  program_ket_of_eq stream _ environment _ _ address
    (Native.inverseMacProgram_canonical ports control environment source target multiplier
      sourceCanonical targetCanonical retained)

lemma subtractSquareProgram_canonical (stream : Fin 2) (control : Native.Control)
    (environment : OracleModel.empty.Interpretation) (source target : Word)
    (sourceCanonical : Canonical source) (targetCanonical : Canonical target)
    (retained : Placement.Rest Native.squarePorts) (address : Address) :
    (program stream (Native.subtractSquareProgram control)).applyNormalized environment
        (ket (streamInput stream (Native.arithmeticState Native.squarePorts source target
          Horner.zeroWord retained) address)) =
      ket (streamInput stream (Native.arithmeticState Native.squarePorts source
        (Accumulate.Inverse.differenceWord source source target
          ((Native.controlBit Native.squarePorts control).get retained))
        Horner.zeroWord retained) address) :=
  program_ket_of_eq stream _ environment _ _ address
    (Native.subtractSquareProgram_canonical control environment source target
      sourceCanonical targetCanonical retained)

def referenceOperator (stream : Fin 2) (body : Native.Circuit)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator ((QubitLayout.canonical encoding.width).toQuantum.register.prod Reference) :=
  UnitaryOperator.prodTensor ((program stream body).matrix environment)
    (1 : UnitaryOperator Reference)

def referenceVector {Reference : Register} {Index : Type} [Fintype Index]
    (states : Index → Raw) (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertVector ((QubitLayout.canonical encoding.width).toQuantum.register.prod Reference) :=
  ∑ index, amplitude index • (NormalizedVector.ket
    (R := (QubitLayout.canonical encoding.width).toQuantum.register.prod Reference)
    ((QubitLayout.canonical _).basisEquiv.symm (encoding.encode (states index)),
      reference index)).vec

/-- The same whole physical body preserves every admitted coherent sum with arbitrary Reference. -/
lemma coherent_of_basis (stream : Fin 2) (body : Native.Circuit)
    (environment : OracleModel.empty.Interpretation) {Reference : Register}
    {Index : Type} [Fintype Index] (initial final : Index → Frame.Raw)
    (address : Index → Address)
    (actual : ∀ index, body.applyNormalized environment (Native.ket (initial index)) =
      Native.ket (final index))
    (reference : Index → Reference.Index) (amplitude : Index → ℂ) :
    HilbertOperator.applyVec (referenceOperator stream body environment Reference)
        (referenceVector (fun index => streamInput stream (initial index) (address index))
          reference amplitude) =
      referenceVector (fun index => streamInput stream (final index) (address index))
        reference amplitude :=
  Native.reference_sum_of_actual (program stream body) environment _ _
    (fun index => program_ket_of_eq stream body environment _ _ (address index) (actual index))
    reference amplitude

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
