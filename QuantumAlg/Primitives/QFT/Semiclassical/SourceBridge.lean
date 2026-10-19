/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Mathematics
public import QuantumAlg.Primitives.QFT.Source.FourierMatrix
public import QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Primitives.QFT.Semiclassical.Mathematics
import all QuantumAlg.Core.Measure.Kraus
import all QuantumAlg.Primitives.QFT.Source.Recurrence
import all QuantumAlg.Primitives.QFT.Source.NoSwapMatrix
import all QuantumAlg.Primitives.QFT.Source.Matrix
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Mathematics
import all QuantumAlg.Util.FinPow.BitReverse
import all QuantumAlg.Components.Gates.Operator
import Mathlib.Tactic.NormNum

/-!
# Exact instrument bridge to the recursively composed Fourier source

Input labels are big-endian. The first physical output wire carries the least
significant Fourier-frequency bit. Classical decoding therefore reverses the
physical outcomes, while the retained quantum bank keeps its original wire
order. The final SWAP network of the coherent source has a different bank factor.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical

open QuantumAlg.MeasurementInstrument

noncomputable section

/-- Recursive physical wire tuples expressed in the existing big-endian labels. -/
@[expose] public def binaryEquiv : (n : Nat) → Bits n ≃ Fin (2 ^ n)
  | 0 =>
      { toFun := fun _ => 0
        invFun := fun _ => ()
        left_inv := fun x => by cases x; rfl
        right_inv := fun x => (Fin.fin_one_eq_zero x).symm }
  | n + 1 =>
      (Equiv.prodCongr (Equiv.refl (Fin 2)) (binaryEquiv n)).trans (qftPairEquiv n)

/-- The exact selected diagonal phase from the existing source recurrence. -/
public def feedback (n : Nat) (b : Fin 2) : Matrix (Bits n) (Bits n) Complex :=
  Matrix.diagonal (fun x => if b = 1 then ω (n + 1) ^ (binaryEquiv n x).val else 1)

/-- The actual no-swap source operator, with only its matrix coordinates changed. -/
public def sourceMatrix (oracles : OracleModel) (n : Nat) (environment : oracles.Interpretation) :
    Matrix (Bits n) (Bits n) Complex :=
  fun y x => Source.onBinaryLabels (Source.noSwap oracles n) environment
    (binaryEquiv n y) (binaryEquiv n x)

/-- The generic coherent products equal the actual source word at every width. -/
public lemma qftSemiclassical_coherent_eq_sourceMatrix (oracles : OracleModel)
    (environment : oracles.Interpretation) :
    ∀ n, coherent Gate.HOp feedback n = sourceMatrix oracles n environment := by
  intro n
  induction n with
  | zero =>
      ext y x
      cases y
      cases x
      simp [coherent, sourceMatrix, binaryEquiv, Source.noSwap,
        Source.qftSource_binaryMatrix_identity]
  | succ n ih =>
      ext y x
      rcases y with ⟨b, yt⟩
      rcases x with ⟨c, xt⟩
      change coherentStage Gate.HOp
          (fun a => Matrix.diagonal
            (fun z => if a = 1 then ω (n + 1) ^ (binaryEquiv n z).val else 1))
          (coherent Gate.HOp feedback n) (b, yt) (c, xt) =
        Source.onBinaryLabels (Source.noSwap oracles (n + 1)) environment
          (qftPairEquiv n (b, binaryEquiv n yt))
          (qftPairEquiv n (c, binaryEquiv n xt))
      rw [phaseStage_entry, Source.qftSource_noSwap_succ_binaryMatrix_pair, ih]
      rfl

/-- The physical no-swap row has the explicitly reversed Fourier-frequency label. -/
public lemma qftSemiclassical_coherent_entry (n : Nat) (y x : Bits n) :
    coherent Gate.HOp feedback n y x =
      QFTOperator n (qftReverseBits n (binaryEquiv n y)) (binaryEquiv n x) := by
  rw [qftSemiclassical_coherent_eq_sourceMatrix OracleModel.empty OracleModel.emptyInterpretation]
  exact Source.qftSource_noSwap_binaryMatrix_entry OracleModel.empty n _ _
    OracleModel.emptyInterpretation

/-- Exact row-Kraus equality to the actual source circuit, without tracing out a reference. -/
public lemma qftSemiclassical_adaptiveKraus_eq_sourceRow
    (oracles : OracleModel) (n : Nat) (y : Bits n) (environment : oracles.Interpretation) :
    adaptiveKraus Gate.HOp feedback n y = rowKraus (sourceMatrix oracles n environment) y := by
  rw [adaptiveKraus_eq_coherent_row, qftSemiclassical_coherent_eq_sourceMatrix]

/-- Full equality keeps the classical outcomes, every physical bank wire, and the reference. -/
public lemma qftSemiclassical_source_retainedInstrument
    (oracles : OracleModel) (n : Nat) {R : Type} [Fintype R] [DecidableEq R]
    (ρ : Matrix (Bits n × R) (Bits n × R) Complex) (environment : oracles.Interpretation) :
    retainedInstrument (fun y : Bits n => y) (adaptiveKraus Gate.HOp feedback n) ρ =
      retainedInstrument (fun y : Bits n => y)
        (fun y => rowKraus (sourceMatrix oracles n environment) y) ρ := by
  rw [adaptive_retainedInstrument_eq_coherent, qftSemiclassical_coherent_eq_sourceMatrix]

/-- Physical output bits corresponding to a canonical Fourier frequency. -/
public def frequencyBits (n : Nat) (y : Fin (2 ^ n)) : Bits n :=
  (binaryEquiv n).symm (qftReverseBits n y)

/-- Classical decoding does not move the retained quantum wires. -/
public lemma qftSemiclassical_frequencyBits_physicalLabel (n : Nat)
    (y : Fin (2 ^ n)) :
    binaryEquiv n (frequencyBits n y) = qftReverseBits n y := by
  exact (binaryEquiv n).apply_symm_apply _

/-- The head of the physical output tuple is the least significant frequency bit. -/
public lemma qftSemiclassical_frequency_head_lsb (n : Nat) (b : Fin 2) (tail : Bits n) :
    (qftReverseBits (n + 1) (binaryEquiv (n + 1) (b, tail))).val =
      2 * (qftReverseBits n (binaryEquiv n tail)).val + b.val := by
  exact qftReverseBits_pair n b (binaryEquiv n tail)

/-- Adaptive measurement rows indexed by the decoded classical Fourier frequency. -/
public def frequencyKraus (n : Nat) (y : Fin (2 ^ n)) : Matrix Unit (Bits n) Complex :=
  adaptiveKraus Gate.HOp feedback n (frequencyBits n y)

/-- The adaptive branch preserves the exact complex Fourier amplitude. -/
public lemma qftSemiclassical_frequencyKraus_entry (n : Nat) (y : Fin (2 ^ n))
    (x : Bits n) :
    frequencyKraus n y () x = QFTOperator n y (binaryEquiv n x) := by
  unfold frequencyKraus
  rw [adaptiveKraus_eq_coherent_row]
  change coherent Gate.HOp feedback n (frequencyBits n y) x = _
  rw [qftSemiclassical_coherent_entry, qftSemiclassical_frequencyBits_physicalLabel,
    qftReverseBits_involutive]

/-- The same rows are obtained by measuring the full coherent source after its actual swaps. -/
public lemma qftSemiclassical_frequencyKraus_eq_fullSourceRow
    (oracles : OracleModel) (n : Nat) (y : Fin (2 ^ n)) (environment : oracles.Interpretation) :
    frequencyKraus n y =
      rowKraus (fun b x => Source.onBinaryLabels (Source.circuit oracles n) environment
        b (binaryEquiv n x)) y := by
  ext u x
  cases u
  rw [qftSemiclassical_frequencyKraus_entry]
  simp only [rowKraus, Source.qftSource_circuit_binaryMatrix]

/-- The common conditional reference state includes all untouched workspace
and external reference. -/
public def frequencyBranch (n : Nat) (y : Fin (2 ^ n))
    {R : Type} [Fintype R] [DecidableEq R]
    (ρ : Matrix (Bits n × R) (Bits n × R) Complex) : Matrix R R Complex :=
  referenceBranch (frequencyKraus n y) ρ

/-- Before any physical swaps, the measured bank is the reversed frequency basis state. -/
public lemma qftSemiclassical_physicalBank_factor (n : Nat) (y : Fin (2 ^ n))
    {R : Type} [Fintype R] [DecidableEq R]
    (ρ : Matrix (Bits n × R) (Bits n × R) Complex) :
    bankBranch (qftReverseBits n y) (frequencyKraus n y) ρ =
      bankEmbedding (qftReverseBits n y) * frequencyBranch n y ρ *
        (bankEmbedding (qftReverseBits n y)).conjTranspose := by
  exact bankBranch_factor _ _ _

/-- After the full source's actual swaps, the bank has label `y` and the same reference branch. -/
public lemma qftSemiclassical_fullSourceBank_factor (oracles : OracleModel)
    (n : Nat) (y : Fin (2 ^ n)) {R : Type} [Fintype R] [DecidableEq R]
    (ρ : Matrix (Bits n × R) (Bits n × R) Complex) (environment : oracles.Interpretation) :
    bankBranch y (rowKraus (fun b x => Source.onBinaryLabels (Source.circuit oracles n) environment
        b (binaryEquiv n x)) y) ρ =
      bankEmbedding y * frequencyBranch n y ρ * (bankEmbedding y).conjTranspose := by
  rw [← qftSemiclassical_frequencyKraus_eq_fullSourceRow]
  exact bankBranch_factor _ _ _

/-- A reused control and memory bank can reset to another basis state
with the same reference branch. -/
public lemma qftSemiclassical_resetBank_factor (n : Nat) (y : Fin (2 ^ n))
    {B R : Type} [DecidableEq B] [Fintype R] [DecidableEq R] (reset : B)
    (ρ : Matrix (Bits n × R) (Bits n × R) Complex) :
    bankBranch reset (frequencyKraus n y) ρ =
      bankEmbedding reset * frequencyBranch n y ρ * (bankEmbedding reset).conjTranspose := by
  exact bankBranch_factor _ _ _

/-- Conjugated gates use the same physical recursion and negative Fourier phases. -/
public def inverseFrequencyKraus (n : Nat) (y : Fin (2 ^ n)) : Matrix Unit (Bits n) Complex :=
  adaptiveKraus (conjugate Gate.HOp) (fun m b => conjugate (feedback m b)) n
    (frequencyBits n y)

/-- Negative phases give the adjoint Fourier row without reversing the measurement schedule. -/
public lemma qftSemiclassical_inverseFrequencyKraus_entry (n : Nat)
    (y : Fin (2 ^ n)) (x : Bits n) :
    inverseFrequencyKraus n y () x =
      ((QFTOperator n)⁻¹ : UnitaryOperator (Qubits n)) y (binaryEquiv n x) := by
  unfold inverseFrequencyKraus
  rw [adaptiveKraus_eq_coherent_row, coherent_conjugate]
  change star (coherent Gate.HOp feedback n (frequencyBits n y) x) =
    star (QFTOperator n (binaryEquiv n x) y)
  rw [qftSemiclassical_coherent_entry, qftSemiclassical_frequencyBits_physicalLabel,
    qftReverseBits_involutive]
  congr 1
  simp only [QFTOperator_entry, Nat.mul_comm]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical
