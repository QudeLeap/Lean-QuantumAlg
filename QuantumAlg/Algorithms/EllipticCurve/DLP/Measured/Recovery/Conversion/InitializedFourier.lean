/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.Protocol
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.TwoBankFourier

/-!
# Actual four-conversion streaming execution on initialized private columns

The hypothesis below describes only this local input family, fiber by fiber at every
complete original Store. It is not a new public inputDomain premise or an actual
initialization proof. Dirty arithmetic/selector data, result-cell Stores, history and
arbitrary Reference remain unrestricted. The explicitly empty quantum cell-frame factor
stays in ResidualReference; no classical cell frame is erased.

All four conversion factors remain literal, surrounding the coherent Fourier
word of one actual measured path. Different paths are summed only as complete
CP sandwiches. No conversion, arithmetic factor or Fourier row is commuted.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg.Execution (State Store)
open Recovery.Stage.PointCoordinates (Bank ResidualReference)
open Recovery.Stage.PointCoordinates.StageWord (bitBasis)
open Recovery.Stage.PointCoordinates.StageWord.StoredRecursion (storeDensity)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity (Branch traceValid)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths
  (initializedBasis initializedColumns mul_initializedColumns initializedColumns_mul
    fourierBankWord actual_initialized_fourier_store_density)
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Actual C/M/bank coordinates agree with the existing Boolean-memory column coordinates. -/
private lemma bankFirst_joint (width m : Nat) (Reference : Register)
    (control : Fin 2) (memory : Bool) (bank : Bank width m Reference) :
    bankFirstCoordinates width m Reference
        ((Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths.joint width m
          Reference).symm (control, (memory, bank))) =
      (bank, (control, bitBasis memory)) := by
  simp only [bankFirstCoordinates,
    Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths.joint, Equiv.symm_trans,
    Equiv.trans_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
    Equiv.apply_symm_apply, Equiv.symm_symm]
  rfl

/-- J00 is the actual zero-control/false-memory inclusion into the same resident bank. -/
private lemma bankFirst_initializedBasis (width m : Nat) (Reference : Register)
    (bank : Bank width m Reference) :
    bankFirstCoordinates width m Reference (initializedBasis width m Reference bank) =
      (bank, (0, bitBasis false)) := by
  have inclusion : initializedBasis width m Reference bank =
      (Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths.joint width m
        Reference).symm ((0 : Fin 2), (false, bank)) := rfl
  have transported := congrArg (bankFirstCoordinates width m Reference) inclusion
  exact transported.trans (bankFirst_joint width m Reference (0 : Fin 2) false bank)

/-- The actual pair operator preserves J00 and acts by the same complete old common-bank pair. -/
lemma pairOperator_initializedColumns (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register) :
    pairOperator (environment := environment) width m modulus coefficient Reference *
        initializedColumns width m Reference =
      initializedColumns width m Reference *
        Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
          coefficient
          (ResidualReference width m Reference) := by
  ext row columnBank
  obtain ⟨⟨control, memory, rowBank⟩, rfl⟩ :=
    (Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths.joint width m
      Reference).symm.surjective row
  rw [mul_initializedColumns (m := m), initializedColumns_mul (m := m)]
  have block := congrArg
    (fun matrix => matrix (rowBank, (control, bitBasis memory))
      (columnBank, (0, bitBasis false)))
    (pairOperator_bankFirst (environment := environment) width m modulus coefficient Reference)
  change pairOperator (environment := environment) width m modulus coefficient Reference
      ((bankFirstCoordinates width m Reference).symm (rowBank, (control, bitBasis memory)))
      ((bankFirstCoordinates width m Reference).symm (columnBank, (0, bitBasis false))) =
    (if (control, bitBasis memory) = (0, bitBasis false) then
      Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
        coefficient
        (ResidualReference width m Reference) rowBank columnBank else 0) at block
  rw [← bankFirst_joint width m Reference control memory rowBank,
    ← bankFirst_initializedBasis width m Reference columnBank,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply] at block
  simpa only [Prod.mk.injEq, bitBasis.injective.eq_iff] using block

/-- Full arbitrary dirty-bank densities follow the same actual conversion sandwich. -/
lemma pair_initialized_sandwich (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register)
    (density : Matrix (Bank width m Reference) (Bank width m Reference) ℂ) :
    pairOperator (environment := environment) width m modulus coefficient Reference *
        (initializedColumns width m Reference * density *
          (initializedColumns width m Reference).conjTranspose) *
        (pairOperator (environment := environment) width m modulus coefficient
          Reference).conjTranspose =
      initializedColumns width m Reference *
        (Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
          coefficient
            (ResidualReference width m Reference) * density *
          (Recovery.Reference.Converted.bankPairOperator (environment := environment) width
            modulus coefficient
            (ResidualReference width m Reference)).conjTranspose) *
        (initializedColumns width m Reference).conjTranspose := by
  calc
    _ = (pairOperator (environment := environment) width m modulus coefficient Reference *
          initializedColumns width m Reference) * density *
        (pairOperator (environment := environment) width m modulus coefficient Reference *
          initializedColumns width m Reference).conjTranspose := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (initializedColumns width m Reference *
          Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
            coefficient
            (ResidualReference width m Reference)) * density *
        (initializedColumns width m Reference *
          Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
            coefficient
            (ResidualReference width m Reference)).conjTranspose := by
      rw [pairOperator_initializedColumns]
    _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Actual conversion execution transports every original complete Store fiber of the local input
family. -/
lemma pair_initialized_store_density (width m : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : (ZMod modulus.val)ˣ) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal width m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (density : Store (Recovery.Layout.terminal width m) →
      Matrix (Bank width m Reference) (Bank width m Reference) ℂ)
    (initialized : ∀ original : Store (Recovery.Layout.terminal width m),
      storeDensity (m := m) (Reference := Reference) state original = initializedColumns width m
        Reference * density original *
        (initializedColumns width m Reference).conjTranspose)
    (final : Store (Recovery.Layout.terminal width m)) :
    storeDensity ((pairCircuit width m modulus coefficient).execute environment Reference state)
      final =
      initializedColumns width m Reference *
        (Recovery.Reference.Converted.bankPairOperator (environment := environment) width modulus
          coefficient
            (ResidualReference width m Reference) * density final *
          (Recovery.Reference.Converted.bankPairOperator (environment := environment) width
            modulus coefficient
            (ResidualReference width m Reference)).conjTranspose) *
        (initializedColumns width m Reference).conjTranspose := by
  rw [pair_store_density, initialized]
  exact pair_initialized_sandwich width m modulus coefficient Reference (density final)

/-- One coherent measured-path Fourier word with all four literal coordinate conversions retained.
-/
def convertedFourierBankWord {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
    (MeasuredUncompute.InPlaceTarget.modulusWord p) coefficient
      (ResidualReference p.size m Reference) *
    fourierBankWord (environment := environment) E r points Reference path *
    Recovery.Reference.Converted.bankPairOperator (environment := environment) p.size
      (MeasuredUncompute.InPlaceTarget.modulusWord p) coefficient⁻¹
      (ResidualReference p.size m Reference)

/-- The exact chronological factors are Cy Cx W Cy-inverse Cx-inverse, without cancellation. -/
lemma convertedFourierBankWord_four_factors {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register) (path : Fin (2 * m) → Branch p.size m) :
    convertedFourierBankWord (environment := environment) E r points coefficient Reference path =
      Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) p.size
        (MeasuredUncompute.InPlaceTarget.modulusWord p)
        coefficient
          .y (ResidualReference p.size m Reference) *
        Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) p.size
          (MeasuredUncompute.InPlaceTarget.modulusWord p)
          coefficient
          .x (ResidualReference p.size m Reference) *
        fourierBankWord (environment := environment) E r points Reference path *
        Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) p.size
          (MeasuredUncompute.InPlaceTarget.modulusWord p)
          coefficient⁻¹
          .y (ResidualReference p.size m Reference) *
        Recovery.Reference.Converted.bankCoordinateOperator (environment := environment) p.size
          (MeasuredUncompute.InPlaceTarget.modulusWord p)
          coefficient⁻¹
          .x (ResidualReference p.size m Reference) := by
  simp only [convertedFourierBankWord, Recovery.Reference.Converted.bankPairOperator,
    Matrix.mul_assoc]

/-- The real four-conversion wrapper preserves J00 on every legal full-Store path CP fiber.

The initialized premise is a local matrix input shape, not an assertion that
the physical allocator has already produced it. Complete dirty-bank densities
and every original result-cell Store/Reference correlation are unrestricted.
-/
lemma actual_initialized_converted_fourier_store_density {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat} (r : Nat)
    (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (density : Store (Recovery.Layout.terminal p.size m) →
      Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ)
    (initialized : ∀ original : Store (Recovery.Layout.terminal p.size m),
      storeDensity (m := m) (Reference := Reference) state original = initializedColumns p.size m
        Reference * density original *
        (initializedColumns p.size m Reference).conjTranspose)
    (positive : 0 < r) (fits : r ≤ 2 ^ m)
    (final : Store (Recovery.Layout.terminal p.size m)) :
    storeDensity ((convertedStages E r points (Recovery.Layout.order m) coefficient).execute
      environment Reference state) final =
      ∑ path : Fin (2 * m) → Branch p.size m,
        ∑ original : Store (Recovery.Layout.terminal p.size m),
          if traceValid p.size m (2 * m) id path original final then
            initializedColumns p.size m Reference *
              (convertedFourierBankWord (environment := environment) E r points coefficient
                Reference path * density original *
                (convertedFourierBankWord (environment := environment) E r points coefficient
                  Reference path).conjTranspose) *
              (initializedColumns p.size m Reference).conjTranspose
          else 0 := by
  let modulus := MeasuredUncompute.InPlaceTarget.modulusWord p
  let inverse := pairCircuit p.size m modulus coefficient⁻¹
  let forward := pairCircuit p.size m modulus coefficient
  let body := Recovery.Stage.stages E r points (Recovery.Layout.order m)
  let inverseBank := Recovery.Reference.Converted.bankPairOperator (environment := environment)
    p.size modulus coefficient⁻¹
    (ResidualReference p.size m Reference)
  let inverseDensity := fun original => inverseBank * density original * inverseBank.conjTranspose
  have inverseInitialized (original : Store (Recovery.Layout.terminal p.size m)) :
      storeDensity (inverse.execute environment Reference state) original =
        initializedColumns p.size m Reference * inverseDensity original *
          (initializedColumns p.size m Reference).conjTranspose :=
    pair_initialized_store_density p.size m modulus coefficient⁻¹ Reference state density
      initialized original
  have outer := congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal inverse (body.seq forward) environment state final)
  have inner := congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal body forward environment
      (inverse.execute environment Reference state) final)
  change storeDensity ((convertedStages E r points (Recovery.Layout.order m) coefficient).execute
    environment Reference state) final =
      storeDensity ((body.seq forward).execute environment Reference (inverse.execute environment
        Reference state)) final
      at outer
  change storeDensity ((body.seq forward).execute environment Reference
    (inverse.execute environment Reference state)) final =
    storeDensity (forward.execute environment Reference (body.execute environment Reference
      (inverse.execute environment Reference state))) final at inner
  let operator := pairOperator (environment := environment) p.size m modulus coefficient Reference
  refine (outer.trans inner).trans
    ((pair_store_density p.size m modulus coefficient Reference
      (body.execute environment Reference (inverse.execute environment Reference state))
        final).trans ?_)
  refine (congrArg
    (fun density : Matrix ((Recovery.Layout.terminal p.size m).register.prod Reference).Index
        ((Recovery.Layout.terminal p.size m).register.prod Reference).Index ℂ =>
      operator * density * operator.conjTranspose)
    (actual_initialized_fourier_store_density (m := m) E r points Reference
      (inverse.execute environment Reference state) inverseDensity inverseInitialized positive fits
      final)).trans ?_
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro path _
  apply Finset.sum_congr rfl
  intro original _
  by_cases valid : traceValid p.size m (2 * m) id path original final
  · simp only [if_pos valid]
    refine (pair_initialized_sandwich p.size m modulus coefficient Reference
      (fourierBankWord (environment := environment) E r points Reference path * inverseDensity
        original *
        (fourierBankWord (environment := environment) E r points Reference
          path).conjTranspose)).trans ?_
    simp only [convertedFourierBankWord, inverseDensity, inverseBank, modulus,
      Matrix.conjTranspose_mul, Matrix.mul_assoc]
  · simp only [if_neg valid, Matrix.mul_zero, Matrix.zero_mul]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
