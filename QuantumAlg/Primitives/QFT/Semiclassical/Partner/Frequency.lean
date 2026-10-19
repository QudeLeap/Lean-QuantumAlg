/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Partner.Recycling
public import QuantumAlg.Primitives.QFT.Native.Matrix
public import QuantumAlg.Primitives.QFT.Native.Inverse
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Recycling
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Phases
import all QuantumAlg.Primitives.QFT.Semiclassical.SourceBridge
import all QuantumAlg.Primitives.QFT.Semiclassical.Coordinates
import all QuantumAlg.Primitives.QFT.Native.Inverse.FourierMatrix
import all QuantumAlg.Primitives.QFT.Native.FourierMatrix
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Core.Measure.Kraus

/-!
# Complete Fourier output labels and chronological recycled-control records

Source-only candidate: no Lean acceptance is claimed. The old complete native
Fourier circuit includes its real SWAP word. Its measured label is the canonical
frequency, whereas the new physical control outcomes occur in the reversed
order. This mathematical coordinate theorem does not execute, erase, or charge
a classical packing operation. An execution consumer must use its actual paid
packing instruction and prove that it reads the indicated reversed positions.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Partner

noncomputable section

open QuantumAlg.MeasurementInstrument
open scoped Kronecker

variable {S : Register}

/-- The actual complete native circuit, including its final or inverse initial SWAP word. -/
public def fullRows (inverse : Bool) (n : Nat) : Matrix (Fin (2 ^ n)) (Bits n) ℂ :=
  fun frequency input =>
    (if inverse then Native.onBinaryLabels (Native.inverseCircuit .empty n)
      else Native.onBinaryLabels (Native.circuit .empty n))
      OracleModel.emptyInterpretation frequency (binaryEquiv n input)

/-- Every empty-oracle interpretation gives the same complete native Fourier row. -/
public lemma qftPartner_fullRows_native (environment : OracleModel.empty.Interpretation)
    (inverse : Bool) (n : Nat) (frequency : Fin (2 ^ n)) (input : Bits n) :
    (if inverse then Native.onBinaryLabels (Native.inverseCircuit .empty n)
      else Native.onBinaryLabels (Native.circuit .empty n))
      environment frequency (binaryEquiv n input) = fullRows inverse n frequency input := by
  cases Subsingleton.elim environment OracleModel.emptyInterpretation
  rfl

/-- A complete-source frequency is the bit reversal of the chronological physical record. -/
public lemma qftPartner_fullRows_physical (inverse : Bool) (n : Nat)
    (frequency : Fin (2 ^ n)) (input : Bits n) :
    fullRows inverse n frequency input =
      fourierRows inverse n (frequencyBits n frequency) input := by
  rw [qftPartner_fourierRows_entry, qftSemiclassical_frequencyBits_physicalLabel,
    qftReverseBits_involutive]
  cases inverse
  · simp only [fullRows, Bool.false_eq_true, ↓reduceIte,
      Native.qftNative_circuit_binaryMatrix]
  · simp only [fullRows, ↓reduceIte, Native.qftNative_inverseCircuit_binaryMatrix]
    rfl

/-- Old full-bank Kraus operator is extracted from the actual complete native Fourier row. -/
public def fullOldKraus (inverse : Bool) (n : Nat) (operators : Fin n → HilbertOperator S)
    (frequency : Fin (2 ^ n)) : HilbertOperator S :=
  withReference (rowKraus (fullRows inverse n) frequency) * preparation n operators

/-- The bit reversal changes the label, not the exact conditional partner operator. -/
public lemma qftPartner_fullOldKraus_physical (inverse : Bool) (n : Nat)
    (operators : Fin n → HilbertOperator S) (frequency : Fin (2 ^ n)) :
    fullOldKraus inverse n operators frequency =
      oldKraus inverse n operators (frequencyBits n frequency) := by
  have row : rowKraus (fullRows inverse n) frequency =
      rowKraus (fourierRows inverse n) (frequencyBits n frequency) := by
    ext point input
    exact qftPartner_fullRows_physical inverse n frequency input
  rw [fullOldKraus, row]
  rfl

/-- Canonical full-source output frequency and native recycled phases have equal exact Kraus. -/
public lemma qftPartner_fullOldKraus_eq_angleKraus (inverse : Bool) (n : Nat)
    (operators : Fin n → UnitaryOperator S) (frequency : Fin (2 ^ n)) :
    fullOldKraus inverse n (fun index => (operators index : HilbertOperator S)) frequency =
      angleKraus inverse n (fun index => (operators index : HilbertOperator S))
        (fun _ => 0) (frequencyBits n frequency) := by
  rw [qftPartner_fullOldKraus_physical, qftPartner_oldKraus_eq_angleKraus]

/-- Reversing a chronological stream recovers the canonical frequency's MSB coordinates. -/
lemma qftPartner_frequency_reversed_coordinate (n : Nat)
    (frequency : Fin (2 ^ n)) (position : Fin n) :
    tupleCoordinates n (frequencyBits n frequency) position.rev =
      (BinaryBasis.bigEndianEquiv n).symm frequency position := by
  simp only [tupleCoordinates, BinaryBasis.bigEndianEquiv_symm_value,
    qftSemiclassical_frequencyBits_physicalLabel, qftReverseBits_testBit, Fin.rev_rev]

/-- Decoding a physical record and selecting its frequency recovers every physical output bit. -/
public lemma qftPartner_frequencyBits_decode (n : Nat) (record : Bits n) :
    frequencyBits n (qftReverseBits n (binaryEquiv n record)) = record := by
  simp only [frequencyBits, qftReverseBits_involutive, Equiv.symm_apply_apply]

/-- Full old posterior retains the arbitrary reference after removing its measured bank. -/
public def fullSigma (inverse : Bool) (n : Nat) (operators : Fin n → HilbertOperator S)
    (frequency : Fin (2 ^ n)) (Reference : Register)
    (density : HilbertOperator (S.prod Reference)) : HilbertOperator (S.prod Reference) :=
  let kraus : Matrix (S.prod Reference).Index (S.prod Reference).Index ℂ :=
    Matrix.of (fullOldKraus inverse n operators frequency ⊗ₖ (1 : HilbertOperator Reference))
  HMul.hMul
    (α := Matrix (S.prod Reference).Index (S.prod Reference).Index ℂ)
    (β := Matrix (S.prod Reference).Index (S.prod Reference).Index ℂ)
    (γ := Matrix (S.prod Reference).Index (S.prod Reference).Index ℂ)
    (HMul.hMul
      (α := Matrix (S.prod Reference).Index (S.prod Reference).Index ℂ)
      (β := Matrix (S.prod Reference).Index (S.prod Reference).Index ℂ)
      (γ := Matrix (S.prod Reference).Index (S.prod Reference).Index ℂ)
      kraus (Matrix.of density))
    kraus.conjTranspose

public lemma qftPartner_fullSigma_physical (inverse : Bool) (n : Nat)
    (operators : Fin n → HilbertOperator S) (frequency : Fin (2 ^ n)) (Reference : Register)
    (density : HilbertOperator (S.prod Reference)) :
    fullSigma inverse n operators frequency Reference density =
      σ inverse n operators (frequencyBits n frequency) Reference density := by
  simp only [fullSigma, σ, qftPartner_fullOldKraus_physical]
  rfl

/-- Actual measured full-source bank: its basis label is the frequency, including the SWAPs. -/
public def fullOldBankBranch (inverse : Bool) (n : Nat)
    (operators : Fin n → HilbertOperator S) (frequency : Fin (2 ^ n)) (Reference : Register)
    (density : HilbertOperator (S.prod Reference)) :
    Matrix (Fin (2 ^ n) × (S.prod Reference).Index)
      (Fin (2 ^ n) × (S.prod Reference).Index) ℂ :=
  let kraus : Matrix (Fin (2 ^ n) × (S.prod Reference).Index) (S.prod Reference).Index ℂ :=
    HMul.hMul
      (α := Matrix (Fin (2 ^ n) × (S.prod Reference).Index)
        (Bits n × (S.prod Reference).Index) ℂ)
      (β := Matrix (Bits n × (S.prod Reference).Index) (S.prod Reference).Index ℂ)
      (γ := Matrix (Fin (2 ^ n) × (S.prod Reference).Index) (S.prod Reference).Index ℂ)
      (Matrix.of (bankKraus frequency (rowKraus (fullRows inverse n) frequency)))
      (Matrix.of (preparation (S := S.prod Reference) n
        (fun index => operators index ⊗ₖ (1 : HilbertOperator Reference))))
  HMul.hMul
    (α := Matrix (Fin (2 ^ n) × (S.prod Reference).Index) (S.prod Reference).Index ℂ)
    (β := Matrix (S.prod Reference).Index (Fin (2 ^ n) × (S.prod Reference).Index) ℂ)
    (γ := Matrix (Fin (2 ^ n) × (S.prod Reference).Index)
      (Fin (2 ^ n) × (S.prod Reference).Index) ℂ)
    (HMul.hMul
      (α := Matrix (Fin (2 ^ n) × (S.prod Reference).Index) (S.prod Reference).Index ℂ)
      (β := Matrix (S.prod Reference).Index (S.prod Reference).Index ℂ)
      (γ := Matrix (Fin (2 ^ n) × (S.prod Reference).Index) (S.prod Reference).Index ℂ)
      kraus (Matrix.of density))
    kraus.conjTranspose

/-- The old physical bank is `|frequency>`, separately embedded around the common posterior. -/
public lemma qftPartner_fullOldBank_factor (inverse : Bool) (n : Nat)
    (operators : Fin n → HilbertOperator S) (frequency : Fin (2 ^ n)) (Reference : Register)
    (density : HilbertOperator (S.prod Reference)) :
    fullOldBankBranch inverse n operators frequency Reference density =
      bankEmbedding frequency * fullSigma inverse n operators frequency Reference density *
        (bankEmbedding frequency).conjTranspose := by
  have row : rowKraus (fullRows inverse n) frequency =
      rowKraus (fourierRows inverse n) (frequencyBits n frequency) := by
    ext point input
    exact qftPartner_fullRows_physical inverse n frequency input
  have factor : bankKraus frequency (rowKraus (fullRows inverse n) frequency) *
      preparation (S := S.prod Reference) n
        (fun index => operators index ⊗ₖ (1 : HilbertOperator Reference)) =
      bankEmbedding frequency * oldKraus (S := S.prod Reference) inverse n
        (fun index => operators index ⊗ₖ (1 : HilbertOperator Reference))
          (frequencyBits n frequency) := by
    rw [bankKraus, row]
    simp only [oldKraus, Matrix.mul_assoc]
  have conjugated := congrArg
    (fun kraus : Matrix (Fin (2 ^ n) × (S.prod Reference).Index)
        (S.prod Reference).Index ℂ =>
      HMul.hMul
        (α := Matrix (Fin (2 ^ n) × (S.prod Reference).Index) (S.prod Reference).Index ℂ)
        (β := Matrix (S.prod Reference).Index (Fin (2 ^ n) × (S.prod Reference).Index) ℂ)
        (γ := Matrix (Fin (2 ^ n) × (S.prod Reference).Index)
          (Fin (2 ^ n) × (S.prod Reference).Index) ℂ)
        (HMul.hMul
          (α := Matrix (Fin (2 ^ n) × (S.prod Reference).Index) (S.prod Reference).Index ℂ)
          (β := Matrix (S.prod Reference).Index (S.prod Reference).Index ℂ)
          (γ := Matrix (Fin (2 ^ n) × (S.prod Reference).Index) (S.prod Reference).Index ℂ)
          kraus density)
        kraus.conjTranspose) factor
  refine conjugated.trans ?_
  rw [qftPartner_oldKraus_reference, qftPartner_fullSigma_physical]
  simp only [σ, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- New physical zero control has the old complete-source frequency's entire posterior. -/
public lemma qftPartner_fullFrequency_newBank_factor (inverse : Bool) (n : Nat)
    (operators : Fin n → UnitaryOperator S) (frequency : Fin (2 ^ n)) (Reference : Register)
    (density : HilbertOperator (S.prod Reference)) :
    newBankBranch inverse n (fun index => (operators index : HilbertOperator S))
        (frequencyBits n frequency) Reference density =
      bankEmbedding (0 : Fin 2) *
        fullSigma inverse n (fun index => (operators index : HilbertOperator S))
          frequency Reference density * (bankEmbedding (0 : Fin 2)).conjTranspose := by
  rw [qftPartner_fullSigma_physical]
  exact qftPartner_newBank_factor inverse n operators _ Reference density

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Partner
