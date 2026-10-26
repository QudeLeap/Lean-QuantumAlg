/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Coordinates
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Reset.Zero
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Support.Wires

/-! # The actual reset record on a complete zero-bank point ket -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

attribute [local irreducible] modulus sourceBlank Inversion.Seed.blank

private lemma digit_zero_of_flags_address
    (stream : Fin 2) (width : Nat) (bounded : width ≤ 15) (bit : Fin (width + 1))
    (raw : Raw) (flags : raw.1.2 = (false, false, false)) (address : raw.2 = 0) :
    (Enable.digitBit stream width bounded bit).get raw = false := by
  cases bit using Fin.cases with
  | zero =>
      change (streamBit stream).get raw = false
      unfold streamBit
      split
      · rw [firstStreamBit_get, flags]
      · rw [secondStreamBit_get, flags]
  | succ bit =>
      change (addressBit ⟨bit.val, lt_of_lt_of_le bit.isLt bounded⟩).get raw = false
      rw [addressBit_get, address]
      simp only [Fin.val_zero, Nat.zero_testBit]

private lemma sourceBlank_digit_zero (stream : Fin 2) (width : Nat) (bounded : width ≤ 15)
    (bit : Fin (width + 1))
    (input numerator : Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size)) :
    (Enable.digitBit stream width bounded bit).get
        (sourceBlank input numerator (false, false, false) 0) = false := by
  exact digit_zero_of_flags_address stream width bounded bit _
    (sourceBlank_flags input numerator (false, false, false) 0)
    (sourceBlank_address input numerator (false, false, false) 0)

private lemma physical_bank_zero_of_digit {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex) (raw : Raw)
    (reads : ∀ bit, (Enable.digitBit index.stream index.lowerWidth
      index.lowerWidth_bound bit).get raw = false) :
    (bankCoordinates (parameters.ports index).wires (parameters.ports index).qubits
      (parameters.physicalLabel raw)).1 = Partner.zeroBits (index.lowerWidth + 1) := by
  apply (window_source_bank_zero_iff (parameters.ports index).wires
    (parameters.ports index).qubits _).mpr
  intro bit
  apply Fin.ext
  change (parameters.physicalLabel raw (parameters.wire index bit)).val = 0
  exact (Sampling.placedLabel_bit encoding (QubitLayout.canonical encoding.width)
    parameters.sameWires
    (Enable.digitBit index.stream index.lowerWidth index.lowerWidth_bound bit) raw).trans (by
      rw [reads bit]
      rfl)

private lemma sourceBlank_zero_bank {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (input numerator : Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size)) :
    (bankCoordinates (parameters.ports index).wires (parameters.ports index).qubits
      (parameters.physicalLabel (sourceBlank input numerator (false, false, false) 0))).1 =
        Partner.zeroBits (index.lowerWidth + 1) :=
  physical_bank_zero_of_digit parameters index _ (fun bit =>
    sourceBlank_digit_zero index.stream index.lowerWidth index.lowerWidth_bound bit input numerator)

private lemma basis_wire_supported {ctx : RuntimeCtx .quantum} {Reference : Register}
    {Record : Type} [Fintype Record] [DecidableEq Record]
    (original : Record) (label : ctx.register.Index) (reference : Reference.Index)
    (wire : Fin ctx.systemCount) (zero : label wire = 0) :
    ∀ result left right (refLeft refRight : Reference.Index), left wire ≠ 0 →
      ((ExecutionState.ofValue original (DensityOperator.ofPure
        (NormalizedVector.ket (R := ctx.register.prod Reference) (label, reference)))).block
          result).matrix (left, refLeft) (right, refRight) = 0 := by
  intro result left right refLeft refRight different
  have absent : (left, refLeft) ≠ (label, reference) := by
    intro same
    exact different ((congrArg (fun value => value.1 wire) same).trans zero)
  by_cases same : result = original
  · simp only [ExecutionState.ofValue_block, if_pos same, DensityOperator.ofPure_matrix,
      NormalizedVector.ket_apply, if_neg absent, zero_mul]
  · simp only [ExecutionState.ofValue_block, if_neg same, DensityOperator.zero_matrix,
      Matrix.zero_apply]

/-- The original complete State equality, named without changing its records or paths. -/
private def ResetBasisRecord {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register)
    {History : Type} [Fintype History]
    [DecidableEq (Store ctx × (services.HiddenState × History))]
    (original : Store ctx × (services.HiddenState × History))
    (basis : ctx.register.Index) (reference : Reference.Index) : Prop :=
  let initial : State ctx Reference (services.HiddenState × History) :=
    ExecutionState.ofValue original (DensityOperator.ofPure
      (NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)))
  (parameters.reset index).execute environment Reference initial =
    initial.mapClassical (fun entry =>
      let result := parameters.resetParameters.zeroRunRecord (services := services)
        (index.lowerWidth + 1) (parameters.wire index) entry.1
      (result.1, (entry.2.1, (entry.2.2, result.2))))

attribute [local irreducible] ResetBasisRecord

private lemma reset_basis_record {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register)
    {History : Type} [Fintype History]
    [DecidableEq (Store ctx × (services.HiddenState × History))]
    (original : Store ctx × (services.HiddenState × History))
    (basis : ctx.register.Index) (reference : Reference.Index)
    (zero : (bankCoordinates (parameters.ports index).wires
      (parameters.ports index).qubits basis).1 = Partner.zeroBits (index.lowerWidth + 1)) :
    ResetBasisRecord parameters index environment Reference original basis reference := by
  unfold ResetBasisRecord
  let initial : State ctx Reference (services.HiddenState × History) :=
    ExecutionState.ofValue original (DensityOperator.ofPure
      (NormalizedVector.ket (R := ctx.register.prod Reference) (basis, reference)))
  have supported : ∀ bit, QuditShift.WireSupported (parameters.wire index bit) 0 initial := by
    intro bit
    exact basis_wire_supported (ctx := ctx) (Reference := Reference)
      (Record := Store ctx × (services.HiddenState × History)) original basis reference
      (parameters.wire index bit)
      ((window_source_bank_zero_iff (parameters.ports index).wires
        (parameters.ports index).qubits basis).mp zero bit)
  have actual := parameters.reset_zero_record (services := services) index environment
    (Reference := Reference) (History := History) initial supported
  exact actual

private lemma reset_blank_column {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
    (parameters : Sampling.Parameters ctx) (index : Sampling.WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register)
    {History : Type} [Fintype History]
    [DecidableEq (Store ctx × (services.HiddenState × History))]
    (original : Store ctx × (services.HiddenState × History))
    (input numerator : Fin (2 ^ PrimeFieldShortWeierstrass.Arithmetic.P256.modulus.size))
    (source : Sampling.SourceRegister.Index) (reference : Reference.Index) :
    ResetBasisRecord parameters index environment (Sampling.SourceRegister.prod Reference)
      original (parameters.physicalLabel (sourceBlank input numerator (false, false, false) 0))
      (source, reference) := by
  exact reset_basis_record (ctx := ctx) (services := services) parameters index environment
    (Sampling.SourceRegister.prod Reference) (History := History) original
    (parameters.physicalLabel (sourceBlank input numerator (false, false, false) 0))
    (source, reference) (sourceBlank_zero_bank parameters index input numerator)


end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
