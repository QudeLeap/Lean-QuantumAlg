/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.CoherentBankFamily
import Mathlib.Data.Fintype.BigOperators

/-!
# Rectangular free-source columns on the exact legal actual paths

Preparation is separated from the literal Fourier and arithmetic columns.
The source coordinates are mathematical indices; no source register is
allocated by the runtime. The same actual complete Store and path labels are
retained, with their trace-validity predicate, before any CP sum is formed.

These identities preserve arbitrary matrices and all external Reference
entries. They do not assert the free-source family Gram identity, a selected
contractive effect, good-component agreement, or a success floor. Completeness
still requires the internal point-family and full-frequency proofs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
namespace FreeSourceFamily

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma conditional_sum_subtype {Label Value : Type}
    [Fintype Label] [AddCommMonoid Value]
    (predicate : Label → Prop) (term : Label → Value) :
    (∑ label, if predicate label then term label else 0) =
      ∑ label : Subtype predicate, term label.val := by
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype _ (fun _ => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]) term

open QuantumAlg QuantumAlg.Execution
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (Bits binaryEquiv)
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.Partner (fourierRows)
open Recovery.Stage.PointCoordinates (Bank)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch traceValid)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity.ActualFeedback (blockOutput)

/-- Both complete virtual exponent tuples precede the unchanged entire bank. -/
def sourceRegister (width m : Nat) (Reference : Register) : Register where
  Index := (Bits m × Bits m) × Bank width m Reference
  fintype := inferInstance
  decEq := inferInstance

/-- Preparation retains its original second-times-first scalar order. -/
def preparationAmplitude (m r : Nat) (source : Bits m × Bits m) : ℂ :=
  ((if (binaryEquiv m source.2).val < r then invSqrt r else 0 : ℝ) : ℂ) *
    ((if (binaryEquiv m source.1).val < r then invSqrt r else 0 : ℝ) : ℂ)

/-- Both negative Fourier rows retain the actual path's physical readout labels. -/
def pathFourierCoefficient (width m : Nat) (path : Fin (2 * m) → Branch width m)
    (source : Bits m × Bits m) : ℂ :=
  fourierRows true m (blockOutput width m path true) source.2 *
    fourierRows true m (blockOutput width m path false) source.1

/-- Preparation changes only mathematical source amplitudes, retaining every bank coordinate. -/
def preparationColumns (width m r : Nat) (Reference : Register) :
    Matrix (sourceRegister width m Reference).Index (Bank width m Reference) ℂ :=
  fun output input => preparationAmplitude m r output.1 * if output.2 = input then 1 else 0

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}

/-- The free-source columns contain no preparation support or normalization factors. -/
def freeSourceColumns (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m) :
    Matrix (Bank p.size m Reference) (sourceRegister p.size m Reference).Index ℂ :=
  fun output input => pathFourierCoefficient p.size m path input.1 *
    CoherentBankFamily.sourceWord (environment := environment) (m := m) E points coefficient
      Reference path
      input.1 output input.2

/-- Preparation followed by these same columns is exactly the actual converted Fourier word. -/
lemma freeSourceColumns_preparation (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m) :
    freeSourceColumns (environment := environment) (m := m) E points coefficient Reference path *
        preparationColumns p.size m r Reference =
      convertedFourierBankWord (environment := environment) (m := m) E r points coefficient
        Reference path := by
  rw [CoherentBankFamily.convertedFourierBankWord_source_sum]
  ext row column
  simp only [Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change (∑ input : (Bits m × Bits m) × Bank p.size m Reference,
    freeSourceColumns (environment := environment) (m := m) E points coefficient Reference path
      row input *
      preparationColumns p.size m r Reference input column) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro source _
  change (∑ bank : Bank p.size m Reference,
    (pathFourierCoefficient p.size m path source *
      CoherentBankFamily.sourceWord (environment := environment) (m := m) E points coefficient
        Reference path source row bank) *
        (preparationAmplitude m r source * if bank = column then 1 else 0)) = _
  simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq']
  unfold CoherentBankFamily.sourceCoefficient preparationAmplitude pathFourierCoefficient
  ac_rfl

/-- Every off-diagonal bank entry is kept when preparation is moved into the source density. -/
lemma freeSourceColumns_sandwich (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (path : Fin (2 * m) → Branch p.size m)
    (density : Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ) :
    convertedFourierBankWord (environment := environment) (m := m) E r points coefficient
      Reference path * density *
        (convertedFourierBankWord (environment := environment) (m := m) E r points coefficient
          Reference path).conjTranspose =
      freeSourceColumns (environment := environment) (m := m) E points coefficient Reference path *
        (preparationColumns p.size m r Reference * density *
          (preparationColumns p.size m r Reference).conjTranspose) *
        (freeSourceColumns (environment := environment) (m := m) E points coefficient Reference
          path).conjTranspose := by
  rw [← freeSourceColumns_preparation (m := m) E r points coefficient Reference path]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The CP outcome is a complete final Store together with its actually legal full path. -/
abbrev LegalOutcome (p m : Nat) (original : Store (Recovery.Layout.terminal p.size m)) :=
  Σ final : Store (Recovery.Layout.terminal p.size m),
    {path : Fin (2 * m) → Branch p.size m //
      traceValid p.size m (2 * m) id path original final}

/-- No invalid raw Store path is admitted as a Kraus outcome. -/
def legalColumns (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (original : Store (Recovery.Layout.terminal p.size m))
    (outcome : LegalOutcome p m original) :
    Matrix (Bank p.size m Reference) (sourceRegister p.size m Reference).Index ℂ :=
  freeSourceColumns (environment := environment) (m := m) E points coefficient Reference
    outcome.2.val

/-- Exact CP selection retains all legal labels, without identifying distinct outcomes. -/
lemma selected_legalColumns_sum (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size m))
    (selected : Store (Recovery.Layout.terminal p.size m) → (Fin (2 * m) → Branch p.size m) → Prop)
    (density : Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ) :
    (∑ final : Store (Recovery.Layout.terminal p.size m),
      ∑ path : Fin (2 * m) → Branch p.size m,
        if traceValid p.size m (2 * m) id path original final then
          if selected final path then
            convertedFourierBankWord (environment := environment) (m := m) E r points coefficient
              Reference path * density *
              (convertedFourierBankWord (environment := environment) (m := m) E r points coefficient
                Reference path).conjTranspose
          else 0
        else 0) =
      ∑ outcome : LegalOutcome p m original,
        if selected outcome.1 outcome.2.val then
          legalColumns (environment := environment) (m := m) E points coefficient Reference
            original outcome *
            (preparationColumns p.size m r Reference * density *
              (preparationColumns p.size m r Reference).conjTranspose) *
            (legalColumns (environment := environment) (m := m) E points coefficient Reference
              original outcome).conjTranspose
        else 0 := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro final _
  rw [conditional_sum_subtype]
  apply Finset.sum_congr rfl
  intro path _
  by_cases chosen : selected final path.val
  · simp only [if_pos chosen, legalColumns]
    exact freeSourceColumns_sandwich (m := m) E r points coefficient Reference path.val density
  · simp only [if_neg chosen]

/-- The literal output bank density has exactly these legal free-source CP summands. -/
lemma outputBankDensity_legalColumns (fieldTail : Nat) (seed : AffinePoint E) (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (final : Store (Recovery.Layout.terminal p.size m)) :
    OutputBankDensity.outputBankDensity (environment := environment) E fieldTail m seed r points
      coefficient state
        predicate final =
      ∑ original : Store (Recovery.Layout.terminal p.size m),
        ∑ path : {path : Fin (2 * m) → Branch p.size m //
            traceValid p.size m (2 * m) id path original final},
          legalColumns (environment := environment) (m := m) E points coefficient Reference
            original ⟨final, path⟩ *
            (preparationColumns p.size m r Reference *
              Recovery.Initialization.HistoryColumns.actualHistoryBankDensity (environment :=
                environment) E fieldTail m seed
                state predicate original *
              (preparationColumns p.size m r Reference).conjTranspose) *
            (legalColumns (environment := environment) (m := m) E points coefficient Reference
              original
              ⟨final, path⟩).conjTranspose := by
  unfold OutputBankDensity.outputBankDensity
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [conditional_sum_subtype]
  apply Finset.sum_congr rfl
  intro path _
  exact freeSourceColumns_sandwich (m := m) E r points coefficient Reference path.val _

end

end FreeSourceFamily
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
