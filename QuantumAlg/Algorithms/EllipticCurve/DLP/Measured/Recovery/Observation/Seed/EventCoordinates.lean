/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.Actual.ReferenceEvent
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.BinarySourceGeometry
import all QuantumAlg.Core.Base.Gate.Effect.Extension

/-!
# The actual reset seed event in original coherent source coordinates

The original exponent pair and arbitrary external Reference embed into the
literal actual free-source bank. This mathematical placement retains the
actual reset arithmetic label, zero selector and unique empty quantum frame.
Every original complete Store and its event effect remain separate.

The preparation sandwich and compressed effect have exactly the existing
pure Reference component's trace. These are coordinate identities, with no
physical preparation, caller condition, selected floor or retirement claim.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace SeedEventCoordinates

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma rectangular_pure_sandwich {Source Target : Register}
    (columns : Matrix Target.Index Source.Index ℂ)
    (input : NormalizedVector Source) (output : NormalizedVector Target)
    (same : columns.toEuclideanLin input.vec = output.vec) :
    columns * (DensityOperator.ofPure input).matrix * columns.conjTranspose =
      (DensityOperator.ofPure output).matrix := by
  have multiplied : columns.mulVec (fun index => input index) = fun index => output index := by
    exact congrArg WithLp.ofLp same
  change columns * Matrix.vecMulVec (fun index => input index) (fun index => star (input index)) *
    columns.conjTranspose = Matrix.vecMulVec (fun index => output index)
      (fun index => star (output index))
  rw [Matrix.mul_vecMulVec, multiplied, Matrix.vecMulVec_mul]
  ext row column
  change output row * (∑ index, star (input index) * star (columns column index)) =
    output row * star (output column)
  congr 1
  calc
    (∑ index, star (input index) * star (columns column index)) =
        star (∑ index, input index * columns column index) := by
      simp only [star_sum, star_mul']
    _ = star (output column) := congrArg star (by
      simpa only [Matrix.mulVec, dotProduct, mul_comm] using congrFun multiplied column)

open QuantumAlg.Execution (Store)
open _root_.QuantumAlg.FiniteCyclicDLP (KnownOrderProblem orderWidth)
open _root_.QuantumAlg.FiniteCyclicDLP.Concrete.BornBridge (exponentState)
open _root_.QuantumAlg.QuantumFourierTransform.Semiclassical (Bits binaryEquiv)
open Recovery.Stage.PointCoordinates (Bank ResidualReference)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.InitializedPaths (initializedBasis joint)
open Recovery.Conversion.FreeSourceFamily
  (preparationColumns preparationAmplitude sourceRegister)
open ECDLP.Measured (idealBranchRegister)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p)

/-- The actual empty quantum frame retains the complete external Reference label. -/
def residualReference (m : Nat) (Reference : Register) (reference : Reference.Index) :
    (ResidualReference p.size m Reference).Index :=
  ((Recovery.Layout.Reference.frameBasis p.size m).symm (), reference)

/-- Equality of these residual labels is exactly equality of the original Reference labels. -/
lemma residualReference_eq_iff (m : Nat) (Reference : Register)
    (left right : Reference.Index) :
    residualReference (p := p) m Reference left =
        residualReference (p := p) m Reference right ↔ left = right := by
  constructor
  · exact fun same => congrArg Prod.snd same
  · exact congrArg (residualReference (p := p) m Reference)

variable [Fact p.Prime]

/-- The seed is the same original reset bank, expressed in the complete actual bank. -/
def seedBank (fieldTail m : Nat) (seed : AffinePoint E) (Reference : Register)
    (reference : Reference.Index) : Bank p.size m Reference :=
  (Recovery.Layout.Reference.bankBasis p.size m Reference).symm
    (Recovery.Reference.Initialization.resetBank E fieldTail m seed Reference reference)

/-- The seed's arithmetic, selector and full residual Reference are literal actual coordinates. -/
lemma seedBank_apply (fieldTail m : Nat) (seed : AffinePoint E) (Reference : Register)
    (reference : Reference.Index) :
    seedBank E fieldTail m seed Reference reference =
      (Recovery.Initialization.resetArithmeticLabel E fieldTail seed,
        (0, residualReference (p := p) m Reference reference)) := rfl

/-- This bank column is precisely the physical reset label beside the same Reference. -/
lemma seedBank_initializedBasis (fieldTail m : Nat) (seed : AffinePoint E)
    (Reference : Register) (reference : Reference.Index) :
    initializedBasis p.size m Reference (seedBank E fieldTail m seed Reference reference) =
      (Recovery.Initialization.newResetLabel E fieldTail m seed, reference) :=
  Recovery.Initialization.newResetLabel_initializedBasis E fieldTail m seed Reference reference

/-- The complete external Reference is not identified with any other seed column. -/
lemma seedBank_injective (fieldTail m : Nat) (seed : AffinePoint E) (Reference : Register) :
    Function.Injective (seedBank E fieldTail m seed Reference) := by
  intro left right same
  have physical := congrArg (initializedBasis p.size m Reference) same
  rw [seedBank_initializedBasis, seedBank_initializedBasis] at physical
  exact congrArg Prod.snd physical

private lemma initializedBasis_injective (width m : Nat) (Reference : Register) :
    Function.Injective (initializedBasis width m Reference) := by
  intro left right same
  have pair : ((0 : Fin 2), (false, left)) = (0, (false, right)) :=
    (joint width m Reference).symm.injective same
  exact congrArg (fun label => label.2.2) pair

/-- Zero extension of an arbitrary coherent Reference is the literal physical seed slice. -/
lemma seedExtension_apply (fieldTail m : Nat) (seed : AffinePoint E)
    {Reference : Register} (input : HilbertVector Reference) (bank : Bank p.size m Reference) :
    Effect.extensionVector (R := BinarySourceGeometry.bankRegister p.size m Reference)
      (S := Reference) (seedBank E fieldTail m seed Reference) input bank =
      NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
          (Recovery.Initialization.newResetLabel E fieldTail m seed)
          (initializedBasis p.size m Reference bank).1 *
        input (initializedBasis p.size m Reference bank).2 := by
  classical
  by_cases physical : (initializedBasis p.size m Reference bank).1 =
      Recovery.Initialization.newResetLabel E fieldTail m seed
  · let reference := (initializedBasis p.size m Reference bank).2
    have pair : initializedBasis p.size m Reference bank =
        (Recovery.Initialization.newResetLabel E fieldTail m seed, reference) :=
      Prod.ext physical rfl
    have same : seedBank E fieldTail m seed Reference reference = bank :=
      initializedBasis_injective p.size m Reference
        ((seedBank_initializedBasis E fieldTail m seed Reference reference).trans pair.symm)
    calc
      Effect.extensionVector (R := BinarySourceGeometry.bankRegister p.size m Reference)
          (S := Reference) (seedBank E fieldTail m seed Reference) input bank =
          input reference := by
        rw [← same]
        exact Effect.extensionVector_image
          (R := BinarySourceGeometry.bankRegister p.size m Reference) (S := Reference)
          (seedBank E fieldTail m seed Reference)
          (seedBank_injective E fieldTail m seed Reference) input reference
      _ = _ := by rw [NormalizedVector.ket_apply, if_pos physical, one_mul]
  · have outside : ∀ reference : Reference.Index,
        seedBank E fieldTail m seed Reference reference ≠ bank := by
      intro reference same
      apply physical
      exact congrArg Prod.fst
        ((congrArg (initializedBasis p.size m Reference) same.symm).trans
          (seedBank_initializedBasis E fieldTail m seed Reference reference))
    have extension := Effect.extensionVector_apply
      (R := BinarySourceGeometry.bankRegister p.size m Reference) (S := Reference)
      (seedBank E fieldTail m seed Reference) input bank
    have zero : (∑ reference : Reference.Index,
        if seedBank E fieldTail m seed Reference reference = bank then input reference else 0) =
        0 := by
      simp only [outside, if_false, Finset.sum_const_zero]
    have physicalZero :
        NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
            (Recovery.Initialization.newResetLabel E fieldTail m seed)
            (initializedBasis p.size m Reference bank).1 *
          input (initializedBasis p.size m Reference bank).2 = 0 := by
      rw [NormalizedVector.ket_apply, if_neg physical, zero_mul]
    exact extension.trans (zero.trans physicalZero.symm)

/-- This normalized bank vector keeps the whole coherent Reference without branch conditioning. -/
def bankSeedState (fieldTail m : Nat) (seed : AffinePoint E) {Reference : Register}
    (input : NormalizedVector Reference) :
    NormalizedVector (BinarySourceGeometry.bankRegister p.size m Reference) :=
  NormalizedVector.ofVector
    (Effect.extensionVector (R := BinarySourceGeometry.bankRegister p.size m Reference)
      (S := Reference) (seedBank E fieldTail m seed Reference) input.vec)
    ((Effect.norm_extensionVector
      (R := BinarySourceGeometry.bankRegister p.size m Reference) (S := Reference)
      (seedBank E fieldTail m seed Reference)
      (seedBank_injective E fieldTail m seed Reference) input.vec).trans input.norm_eq_one)

/-- The initialized physical pure seed block is exactly this full bank pure density. -/
lemma bankSeedState_pure_matrix (fieldTail m : Nat) (seed : AffinePoint E)
    {Reference : Register} (input : NormalizedVector Reference) :
    (DensityOperator.ofPure
        (NormalizedVector.prodTensor
          (NormalizedVector.ket (R := (Recovery.Layout.terminal p.size m).register)
            (Recovery.Initialization.newResetLabel E fieldTail m seed))
          input)).matrix.submatrix
        (initializedBasis p.size m Reference) (initializedBasis p.size m Reference) =
      (DensityOperator.ofPure (bankSeedState E fieldTail m seed input)).matrix := by
  ext row column
  simp only [Matrix.submatrix_apply, DensityOperator.ofPure_matrix,
    NormalizedVector.prodTensor_apply]
  change _ = Effect.extensionVector (R := BinarySourceGeometry.bankRegister p.size m Reference)
      (S := Reference) (seedBank E fieldTail m seed Reference) input.vec row *
    star (Effect.extensionVector (R := BinarySourceGeometry.bankRegister p.size m Reference)
      (S := Reference) (seedBank E fieldTail m seed Reference) input.vec column)
  rw [seedExtension_apply, seedExtension_apply]

/-- Actual preparation produces the same normalized binary source, including source padding. -/
lemma preparation_sandwich (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (seed : AffinePoint E) {Reference : Register}
    (input : NormalizedVector Reference) :
    preparationColumns p.size (orderWidth problem) problem.order Reference *
        (DensityOperator.ofPure
          (NormalizedVector.prodTensor
            (NormalizedVector.ket
              (R := (Recovery.Layout.terminal p.size (orderWidth problem)).register)
              (Recovery.Initialization.newResetLabel E fieldTail (orderWidth problem) seed))
            input)).matrix.submatrix
          (initializedBasis p.size (orderWidth problem) Reference)
          (initializedBasis p.size (orderWidth problem) Reference) *
        (preparationColumns p.size (orderWidth problem) problem.order Reference).conjTranspose =
      (DensityOperator.ofPure (BinarySourceGeometry.sourceState problem
        (bankSeedState E fieldTail (orderWidth problem) seed input))).matrix := by
  rw [bankSeedState_pure_matrix]
  exact rectangular_pure_sandwich
    (Source := BinarySourceGeometry.bankRegister p.size (orderWidth problem) Reference)
    (Target := sourceRegister p.size (orderWidth problem) Reference)
    (preparationColumns p.size (orderWidth problem) problem.order Reference)
    (bankSeedState E fieldTail (orderWidth problem) seed input)
    (BinarySourceGeometry.sourceState problem
      (bankSeedState E fieldTail (orderWidth problem) seed input))
    (BinarySourceGeometry.preparationColumns_sourceState problem
      (bankSeedState E fieldTail (orderWidth problem) seed input))

/-- Original first/second exponent labels and Reference occupy their precise seed-bank columns. -/
def sourceEmbedding (problem : KnownOrderProblem E.GroupPoint) (fieldTail : Nat)
    (seed : AffinePoint E) (Reference : Register) :
    ((idealBranchRegister problem).prod Reference).Index →
      (sourceRegister p.size (orderWidth problem) Reference).Index :=
  fun label =>
    (((binaryEquiv (orderWidth problem)).symm label.1.1,
      (binaryEquiv (orderWidth problem)).symm label.1.2),
      seedBank E fieldTail (orderWidth problem) seed Reference label.2)

/-- Injectivity retains the two original exponent labels and all external Reference correlations. -/
lemma sourceEmbedding_injective (problem : KnownOrderProblem E.GroupPoint) (fieldTail : Nat)
    (seed : AffinePoint E) (Reference : Register) :
    Function.Injective (sourceEmbedding E problem fieldTail seed Reference) := by
  intro left right same
  apply Prod.ext
  · apply Prod.ext
    · exact (binaryEquiv (orderWidth problem)).symm.injective
        (congrArg (fun label => label.1.1) same)
    · exact (binaryEquiv (orderWidth problem)).symm.injective
        (congrArg (fun label => label.1.2) same)
  · exact seedBank_injective E fieldTail (orderWidth problem) seed Reference
      (congrArg Prod.snd same)

private lemma sourceEmbedding_eq_iff (problem : KnownOrderProblem E.GroupPoint)
    (fieldTail : Nat) (seed : AffinePoint E) (Reference : Register)
    (label : ((idealBranchRegister problem).prod Reference).Index)
    (output : (sourceRegister p.size (orderWidth problem) Reference).Index) :
    sourceEmbedding E problem fieldTail seed Reference label = output ↔
      label.1 = (binaryEquiv (orderWidth problem) output.1.1,
        binaryEquiv (orderWidth problem) output.1.2) ∧
      seedBank E fieldTail (orderWidth problem) seed Reference label.2 = output.2 := by
  constructor
  · intro same
    refine ⟨Prod.ext ?_ ?_, congrArg Prod.snd same⟩
    · exact ((binaryEquiv (orderWidth problem)).apply_symm_apply label.1.1).symm.trans
        (congrArg (fun value : (sourceRegister p.size (orderWidth problem) Reference).Index =>
          binaryEquiv (orderWidth problem) value.1.1) same)
    · exact ((binaryEquiv (orderWidth problem)).apply_symm_apply label.1.2).symm.trans
        (congrArg (fun value : (sourceRegister p.size (orderWidth problem) Reference).Index =>
          binaryEquiv (orderWidth problem) value.1.2) same)
  · rintro ⟨branch, bank⟩
    refine Prod.ext (Prod.ext ?_ ?_) bank
    · exact (congrArg (fun value : (idealBranchRegister problem).Index =>
        (binaryEquiv (orderWidth problem)).symm value.1) branch).trans
          ((binaryEquiv (orderWidth problem)).symm_apply_apply output.1.1)
    · exact (congrArg (fun value : (idealBranchRegister problem).Index =>
        (binaryEquiv (orderWidth problem)).symm value.2) branch).trans
          ((binaryEquiv (orderWidth problem)).symm_apply_apply output.1.2)

omit [Fact p.Prime] in
private lemma originalSource_apply (problem : KnownOrderProblem E.GroupPoint)
    {Reference : Register} (input : NormalizedVector Reference)
    (branch : (idealBranchRegister problem).Index) (reference : Reference.Index) :
    SourceGeometry.sourceState problem input (branch, reference) =
      preparationAmplitude (orderWidth problem) problem.order
        ((binaryEquiv (orderWidth problem)).symm branch.1,
          (binaryEquiv (orderWidth problem)).symm branch.2) * input reference := by
  change (exponentState problem branch.1 *
    exponentState problem branch.2) * input reference = _
  rw [BinarySourceGeometry.original_range_amplitude,
    BinarySourceGeometry.original_range_amplitude]
  simp only [preparationAmplitude, Equiv.apply_symm_apply]
  exact congrArg (fun amplitude : ℂ => amplitude * input reference) (mul_comm _ _)

set_option maxHeartbeats 400000 in
-- The complete coherent source and Reference sum need this bounded local proof budget.
/-- The original full coherent source extends to the exact actual prepared seed source. -/
lemma sourceExtension (problem : KnownOrderProblem E.GroupPoint) (fieldTail : Nat)
    (seed : AffinePoint E) {Reference : Register} (input : NormalizedVector Reference) :
    Effect.extensionVector (R := sourceRegister p.size (orderWidth problem) Reference)
        (S := (idealBranchRegister problem).prod Reference)
        (sourceEmbedding E problem fieldTail seed Reference)
        (SourceGeometry.sourceState problem input).vec =
      (BinarySourceGeometry.sourceState problem
        (bankSeedState E fieldTail (orderWidth problem) seed input)).vec := by
  classical
  apply WithLp.ofLp_injective
  funext output
  let branch : (idealBranchRegister problem).Index :=
    (binaryEquiv (orderWidth problem) output.1.1,
      binaryEquiv (orderWidth problem) output.1.2)
  let included : Reference.Index → Prop := fun reference =>
    seedBank E fieldTail (orderWidth problem) seed Reference reference = output.2
  let original : (idealBranchRegister problem).Index → Reference.Index → ℂ :=
    fun exponent reference => SourceGeometry.sourceState problem input (exponent, reference)
  let amplitude : ℂ := preparationAmplitude (orderWidth problem) problem.order output.1
  have sourceSum :
      (∑ index : (idealBranchRegister problem).Index × Reference.Index,
        if sourceEmbedding E problem fieldTail seed Reference index = output then
          original index.1 index.2 else 0) =
        ∑ reference : Reference.Index,
          if included reference then original branch reference else 0 := by
    calc
      _ = ∑ exponent : (idealBranchRegister problem).Index, ∑ reference : Reference.Index,
          if exponent = branch ∧ included reference then original exponent reference else 0 :=
        (Fintype.sum_prod_type (fun index :
          (idealBranchRegister problem).Index × Reference.Index =>
            if sourceEmbedding E problem fieldTail seed Reference index = output then
              original index.1 index.2 else 0)).trans (by
                apply Finset.sum_congr rfl
                intro exponent _
                apply Finset.sum_congr rfl
                intro reference _
                exact if_congr
                  (sourceEmbedding_eq_iff E problem fieldTail seed Reference
                    (exponent, reference) output) rfl rfl)
      _ = _ := by
        simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_const_zero, Fintype.sum_ite_eq']
  have originalAmplitude (reference : Reference.Index) :
      original branch reference = amplitude * input reference :=
    (originalSource_apply (E := E) problem input branch reference).trans
      (congrArg (fun value : Bits (orderWidth problem) × Bits (orderWidth problem) =>
        preparationAmplitude (orderWidth problem) problem.order value * input reference)
          (Prod.ext ((binaryEquiv (orderWidth problem)).symm_apply_apply output.1.1)
            ((binaryEquiv (orderWidth problem)).symm_apply_apply output.1.2)))
  have sumAmplitude :
      (∑ reference : Reference.Index, if included reference then original branch reference else 0) =
        amplitude * ∑ reference : Reference.Index,
          if included reference then input reference else 0 := by
    calc
      _ = ∑ reference : Reference.Index,
          if included reference then amplitude * input reference else 0 :=
        Finset.sum_congr rfl (fun reference _ =>
          if_congr Iff.rfl (originalAmplitude reference) rfl)
      _ = _ := by simp only [Finset.mul_sum, mul_ite, mul_zero]
  have bankEntry := Effect.extensionVector_apply
    (R := BinarySourceGeometry.bankRegister p.size (orderWidth problem) Reference)
    (S := Reference) (seedBank E fieldTail (orderWidth problem) seed Reference) input.vec output.2
  have preparedEntry := BinarySourceGeometry.sourceState_apply problem
    (bankSeedState E fieldTail (orderWidth problem) seed input) output
  exact (Effect.extensionVector_apply
    (R := sourceRegister p.size (orderWidth problem) Reference)
    (S := (idealBranchRegister problem).prod Reference)
    (sourceEmbedding E problem fieldTail seed Reference)
    (SourceGeometry.sourceState problem input).vec output).trans
      (sourceSum.trans (sumAmplitude.trans
        ((congrArg (fun value : ℂ => amplitude * value) bankEntry).symm.trans preparedEntry.symm)))

/-- The same actual event is an internal effect on the original branch and external Reference. -/
def sourceEffect (problem : KnownOrderProblem E.GroupPoint) (fieldTail : Nat)
    (seed : AffinePoint E) (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register)
    (original : Store (Recovery.Layout.terminal p.size (orderWidth problem)))
    (event : Store (Recovery.Layout.terminal p.size (orderWidth problem)) → Prop) :
    Effect ((idealBranchRegister problem).prod Reference) :=
  Effect.compress (R := sourceRegister p.size (orderWidth problem) Reference)
    (S := (idealBranchRegister problem).prod Reference)
    (sourceEmbedding E problem fieldTail seed Reference)
    (sourceEmbedding_injective E problem fieldTail seed Reference)
    (ActualSelectedEffect.eventEffect (environment := environment) E points coefficient Reference
      original event)

/-- Compression is the same pure trace already used in the actual Reference spectral mixture. -/
lemma sourceEffect_weight (problem : KnownOrderProblem E.GroupPoint) (fieldTail : Nat)
    (seed : AffinePoint E) (points : Fin (2 * orderWidth problem) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) {Reference : Register}
    (original : Store (Recovery.Layout.terminal p.size (orderWidth problem)))
    (event : Store (Recovery.Layout.terminal p.size (orderWidth problem)) → Prop)
    (input : NormalizedVector Reference) :
    (sourceEffect (environment := environment) E problem fieldTail seed points coefficient
      Reference original event).weight
        (DensityOperator.ofPure (SourceGeometry.sourceState problem input)) =
      ActualReferenceEvent.referenceComponentWeight (environment := environment) E fieldTail seed
        problem.order points
        coefficient original event input := by
  have compressed := ECDLP.Measured.compress_weight_subnormalized
    (R := sourceRegister p.size (orderWidth problem) Reference)
    (S := (idealBranchRegister problem).prod Reference)
    (sourceEmbedding E problem fieldTail seed Reference)
    (sourceEmbedding_injective E problem fieldTail seed Reference)
    (ActualSelectedEffect.eventEffect (environment := environment) E points coefficient Reference
      original event)
    (SourceGeometry.sourceState problem input).vec
    (by rw [(SourceGeometry.sourceState problem input).norm_eq_one])
  rw [Effect.weight_ofSubnormalizedVector, Effect.weight_ofSubnormalizedVector] at compressed
  rw [sourceExtension] at compressed
  unfold ActualReferenceEvent.referenceComponentWeight
  rw [preparation_sandwich]
  change (sourceEffect (environment := environment) E problem fieldTail seed points coefficient
    Reference original event).weight
    (DensityOperator.ofPure (SourceGeometry.sourceState problem input)) =
      (ActualSelectedEffect.eventEffect (environment := environment) E points coefficient
        Reference original event).weight
        (DensityOperator.ofPure (BinarySourceGeometry.sourceState problem
          (bankSeedState E fieldTail (orderWidth problem) seed input)))
  rw [Effect.weight_ofPure, Effect.weight_ofPure]
  exact compressed

end

end SeedEventCoordinates
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
