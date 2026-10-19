/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.PartnerComparison
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Clean.Subspace
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Phases
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Group.Action
import all QuantumAlg.Util.Nat.FixedWidth.Unit.Exponentiation
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# The old actual full-word arithmetic on its complete clean unit span

The old operator is the actual existing
compiledGroupActionProgram, with its original two full exponent banks and shared
two-word arithmetic workspace. Its already derived clean ket action is reused
through CleanSubspace.group_intertwines. The shared QFT orderedWord at the exact
MSB addresses is shown to implement the same unit power, so the two operators
agree on every coherent clean input and every mixed/reference block.

Only multiplication of the source modular units is reordered. The total dirty
arithmetic matrices are not asserted to commute. No ordered abstract operator
is substituted for the old actual circuit without an execution equation. The
old actual Hadamard preparation, complete native inverse-QFT readout and real
stored measurement instrument still require the next execution bridges.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordAction

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open QuantumFourierTransform.Semiclassical
open Nat.FixedWidth.UnitExponentiation
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {width : Nat} (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]

private lemma translation_one :
    (Carrier.translation modulus 1 : HilbertOperator (Carrier.units modulus.val)) = 1 := by
  ext row column
  have inverseOne (seed : (Carrier.units modulus.val).Index) :
      (Equiv.mulLeft (1 : (ZMod modulus.val)ˣ)).symm seed = seed := by
    change (1 : (ZMod modulus.val)ˣ)⁻¹ * seed = seed
    simp only [inv_one, one_mul]
  simp only [Carrier.translation, UnitaryOperator.ofPerm_entry, inverseOne, Matrix.one_apply]

private lemma translation_mul (first second : (ZMod modulus.val)ˣ) :
    (Carrier.translation modulus first : HilbertOperator (Carrier.units modulus.val)) *
        (Carrier.translation modulus second : HilbertOperator (Carrier.units modulus.val)) =
      (Carrier.translation modulus (first * second) :
        HilbertOperator (Carrier.units modulus.val)) := by
  have operators : Carrier.translation modulus first * Carrier.translation modulus second =
      Carrier.translation modulus (first * second) := by
    unfold Carrier.translation
    rw [UnitaryOperator.ofPerm_mul]
    apply congrArg (fun permutation : Equiv.Perm (Carrier.units modulus.val).Index =>
      UnitaryOperator.ofPerm permutation)
    calc
      (Equiv.mulLeft second).symm * (Equiv.mulLeft first).symm =
          Equiv.mulLeft (second⁻¹ * first⁻¹) := by
        rw [Equiv.mulLeft_symm, Equiv.mulLeft_symm, Equiv.mulLeft_mul]
      _ = (Equiv.mulLeft (first * second)).symm := by
        rw [Equiv.mulLeft_symm, mul_inv_rev]
  exact congrArg (fun operator : UnitaryOperator (Carrier.units modulus.val) =>
    (operator : HilbertOperator (Carrier.units modulus.val))) operators

private lemma chronological_translations (choices : List (ZMod modulus.val)ˣ) :
    Partner.chronologicalProduct (choices.map fun unit =>
      (Carrier.translation modulus unit : HilbertOperator (Carrier.units modulus.val))) =
      (Carrier.translation modulus choices.prod : HilbertOperator (Carrier.units modulus.val)) :=
    by
  induction choices with
  | nil => simp only [List.map_nil, Partner.chronologicalProduct, List.prod_nil, translation_one]
  | cons head tail induction =>
      rw [List.map_cons, Partner.chronologicalProduct, induction, translation_mul, List.prod_cons]
      exact congrArg (fun unit : (ZMod modulus.val)ˣ =>
        (Carrier.translation modulus unit : HilbertOperator (Carrier.units modulus.val)))
        (mul_comm tail.prod head)

private lemma selected_translation (unit : (ZMod modulus.val)ˣ) (bit : Fin 2) :
    Partner.selected
        (Carrier.translation modulus unit : HilbertOperator (Carrier.units modulus.val)) bit =
      (Carrier.translation modulus (if bit = 0 then 1 else unit) :
        HilbertOperator (Carrier.units modulus.val)) := by
  by_cases zero : bit = 0
  · simp only [Partner.selected, zero, if_true, translation_one]
  · simp only [Partner.selected, zero, if_false]

/-- The shared MSB-ordered actual selected translations recover the original full exponent. -/
lemma orderedWord_power (bits : Nat) (unit : (ZMod modulus.val)ˣ) (input : Bits bits) :
    Partner.orderedWord bits
        (fun position => (PartnerComparison.powerOperators modulus bits unit position :
          HilbertOperator (Carrier.units modulus.val))) input =
      (Carrier.translation modulus (unit ^ (binaryEquiv bits input).val) :
        HilbertOperator (Carrier.units modulus.val)) := by
  let choices (position : Fin bits) : (ZMod modulus.val)ˣ :=
    if tupleCoordinates bits input position = 0 then 1 else unit ^ (2 ^ position.rev.val)
  have chosen (position : Fin bits) :
      choices position = selectedUnit unit (binaryEquiv bits input).val position.rev := by
    dsimp only [choices, selectedUnit, stageUnit]
    rw [Partner.tuple_bit]
    generalize tupleCoordinates bits input position = bit
    fin_cases bit <;> rfl
  have product : (∏ position : Fin bits, choices position) =
      unit ^ (binaryEquiv bits input).val := by
    calc
      _ = ∏ position : Fin bits, selectedUnit unit (binaryEquiv bits input).val position.rev := by
        apply Finset.prod_congr rfl
        intro position _
        exact chosen position
      _ = ∏ position : Fin bits, selectedUnit unit (binaryEquiv bits input).val position :=
        Equiv.prod_comp (Fin.revPerm (n := bits))
          (selectedUnit unit (binaryEquiv bits input).val)
      _ = _ := by
        have actual := scheduledUnit_all_eq_pow unit (binaryEquiv bits input)
        simpa only [scheduledUnit, List.map_ofFn, List.prod_ofFn, Function.comp_apply] using actual
  have mapped :
      (List.ofFn fun position : Fin bits => (Carrier.translation modulus (choices position) :
        HilbertOperator (Carrier.units modulus.val))) =
      (List.ofFn choices).map fun unit =>
        (Carrier.translation modulus unit : HilbertOperator (Carrier.units modulus.val)) := by
    simp only [List.map_ofFn, Function.comp_def]
  unfold Partner.orderedWord
  simp only [PartnerComparison.powerOperators, selected_translation]
  change Partner.chronologicalProduct
    (List.ofFn fun position : Fin bits => (Carrier.translation modulus (choices position) :
      HilbertOperator (Carrier.units modulus.val))) = _
  rw [mapped, chronological_translations, List.prod_ofFn, product]

/-- Two literal ordered translation streams, using both original full exponent labels. -/
def orderedSource (m ell : Nat) (generator target : (ZMod modulus.val)ˣ) :
    HilbertOperator (CleanSubspace.carrier m ell modulus.val) :=
  fun row column => if row.1 = column.1 then
    (Partner.orderedWord ell
        (fun position => (PartnerComparison.powerOperators modulus ell target⁻¹ position :
          HilbertOperator (Carrier.units modulus.val))) ((binaryEquiv ell).symm column.1.2) *
      Partner.orderedWord (ell + m)
        (fun position => (PartnerComparison.powerOperators modulus (ell + m) generator position :
          HilbertOperator (Carrier.units modulus.val)))
        ((binaryEquiv (ell + m)).symm column.1.1)) row.2 column.2
    else 0

/-- The ordered source is the same exact permutation already proved for the old actual compiler. -/
lemma sourceAction_ordered (m ell : Nat) (generator target : (ZMod modulus.val)ˣ) :
    (UnitaryOperator.ofPerm (CleanSubspace.action m ell modulus.val generator target).symm :
      HilbertOperator (CleanSubspace.carrier m ell modulus.val)) =
        orderedSource modulus m ell generator target := by
  ext row column
  unfold orderedSource
  rw [orderedWord_power, orderedWord_power, translation_mul]
  simp only [Equiv.apply_symm_apply]
  have coefficient : target⁻¹ ^ column.1.2.val * generator ^ column.1.1.val =
      oracleValue generator target column.1.1.val column.1.2.val := by
    simp only [oracleValue, inv_pow]
    ac_rfl
  rw [coefficient]
  simp only [Carrier.translation, UnitaryOperator.ofPerm_entry]
  have sourceRow : (CleanSubspace.action m ell modulus.val generator target).symm row =
      (row.1, (oracleValue generator target row.1.1.val row.1.2.val)⁻¹ * row.2) := rfl
  have translatedRow :
      (Equiv.mulLeft (oracleValue generator target column.1.1.val column.1.2.val)).symm row.2 =
        (oracleValue generator target column.1.1.val column.1.2.val)⁻¹ * row.2 := rfl
  rw [sourceRow, translatedRow]
  rcases row with ⟨rowBank, rowSeed⟩
  rcases column with ⟨columnBank, columnSeed⟩
  by_cases same : rowBank = columnBank
  · subst columnBank
    simp only [if_true]
    by_cases seedSame :
        (oracleValue generator target rowBank.1.val rowBank.2.val)⁻¹ * rowSeed = columnSeed
    · have pairSame :
          (((rowBank, (oracleValue generator target rowBank.1.val rowBank.2.val)⁻¹ * rowSeed) :
            (CleanSubspace.carrier m ell modulus.val).Index) = (rowBank, columnSeed)) :=
        Prod.ext rfl seedSame
      exact (if_pos pairSame).trans (if_pos seedSame).symm
    · have pairDifferent :
          ¬ (((rowBank, (oracleValue generator target rowBank.1.val rowBank.2.val)⁻¹ * rowSeed) :
            (CleanSubspace.carrier m ell modulus.val).Index) = (rowBank, columnSeed)) := by
        intro reached
        exact seedSame
          (congrArg (fun value : (CleanSubspace.carrier m ell modulus.val).Index => value.2)
            reached)
      exact (if_neg pairDifferent).trans (if_neg seedSame).symm
  · have pairDifferent :
        ¬ (((rowBank, (oracleValue generator target rowBank.1.val rowBank.2.val)⁻¹ * rowSeed) :
          (CleanSubspace.carrier m ell modulus.val).Index) = (columnBank, columnSeed)) := by
      intro reached
      exact same
        (congrArg (fun value : (CleanSubspace.carrier m ell modulus.val).Index => value.1)
          reached)
    exact (if_neg pairDifferent).trans (if_neg same).symm

variable (m ell : Nat) (nontrivial : 1 < modulus.val) (fits : modulus.val < 2 ^ width)

/-- The old actual full-word gates, rather than an abstract replacement, supply this equation. -/
lemma actual_group_ordered (generator target : (ZMod modulus.val)ˣ) :
    let native : HilbertOperator (CleanSubspace.physical m ell width) :=
      ((compiledGroupActionProgram m ell width modulus.val generator target).matrix environment).val
    let embedding : Matrix (CleanSubspace.physical m ell width).Index
        (CleanSubspace.carrier m ell modulus.val).Index ℂ :=
      BasisEmbedding.matrix (CleanSubspace.embedding m ell width modulus.val nontrivial fits)
    let source : HilbertOperator (CleanSubspace.carrier m ell modulus.val) :=
      orderedSource modulus m ell generator target
    native * embedding = embedding * source := by
  simpa only [sourceAction_ordered modulus] using
    CleanSubspace.group_intertwines (environment := environment) m ell width modulus.val generator
      target nontrivial fits

/-- The complete clean span may carry arbitrary coherence with the same external Reference. -/
lemma actual_group_ordered_reference (generator target : (ZMod modulus.val)ˣ)
    (Reference : Register) :
    let native : HilbertOperator ((CleanSubspace.physical m ell width).prod Reference) :=
      (UnitaryOperator.prodTensor
        ((compiledGroupActionProgram m ell width modulus.val generator target).matrix environment)
        (1 : UnitaryOperator Reference)).val
    let embedding : Matrix ((CleanSubspace.physical m ell width).prod Reference).Index
        ((CleanSubspace.carrier m ell modulus.val).prod Reference).Index ℂ :=
      BasisEmbedding.matrix (BasisEmbedding.withReference
        (CleanSubspace.embedding m ell width modulus.val nontrivial fits) Reference)
    let source : HilbertOperator ((CleanSubspace.carrier m ell modulus.val).prod Reference) :=
      orderedSource modulus m ell generator target ⊗ₖ (1 : HilbertOperator Reference)
    native * embedding = embedding * source := by
  have actual := BasisEmbedding.reference_intertwines
    (R := CleanSubspace.physical m ell width)
    (S := CleanSubspace.carrier m ell modulus.val)
    (CleanSubspace.embedding m ell width modulus.val nontrivial fits)
    (UnitaryOperator.ofPerm (CleanSubspace.action m ell modulus.val generator target).symm)
    ((compiledGroupActionProgram m ell width modulus.val generator target).matrix environment)
    (CleanSubspace.group_intertwines (environment := environment) m ell width modulus.val generator
      target nontrivial fits)
    Reference
  let encoding : Matrix ((CleanSubspace.physical m ell width).prod Reference).Index
      ((CleanSubspace.carrier m ell modulus.val).prod Reference).Index ℂ :=
    BasisEmbedding.matrix (BasisEmbedding.withReference
      (CleanSubspace.embedding m ell width modulus.val nontrivial fits) Reference)
  have sourceReference :
      (UnitaryOperator.prodTensor
        (UnitaryOperator.ofPerm (CleanSubspace.action m ell modulus.val generator target).symm)
        (1 : UnitaryOperator Reference)).val =
      (orderedSource modulus m ell generator target ⊗ₖ (1 : HilbertOperator Reference) :
        HilbertOperator ((CleanSubspace.carrier m ell modulus.val).prod Reference)) := by
    simpa only [sourceAction_ordered modulus] using
      BasisEmbedding.reference_operator
        (R := CleanSubspace.carrier m ell modulus.val)
        (UnitaryOperator.ofPerm (CleanSubspace.action m ell modulus.val generator target).symm)
        Reference
  exact actual.trans (congrArg
    (fun operator : HilbertOperator ((CleanSubspace.carrier m ell modulus.val).prod Reference) =>
      encoding * operator) sourceReference)

/-- The old actual arithmetic preserves every mixed/reference entry of this same clean span. -/
lemma actual_group_ordered_mixed (generator target : (ZMod modulus.val)ˣ)
    (Reference : Register)
    (density : HilbertOperator ((CleanSubspace.carrier m ell modulus.val).prod Reference)) :
    let injection := BasisEmbedding.withReference
      (CleanSubspace.embedding m ell width modulus.val nontrivial fits) Reference
    let native : HilbertOperator ((CleanSubspace.physical m ell width).prod Reference) :=
      (UnitaryOperator.prodTensor
        ((compiledGroupActionProgram m ell width modulus.val generator target).matrix environment)
        (1 : UnitaryOperator Reference)).val
    let embedding : Matrix ((CleanSubspace.physical m ell width).prod Reference).Index
        ((CleanSubspace.carrier m ell modulus.val).prod Reference).Index ℂ :=
      BasisEmbedding.matrix injection
    let source : HilbertOperator ((CleanSubspace.carrier m ell modulus.val).prod Reference) :=
      orderedSource modulus m ell generator target ⊗ₖ (1 : HilbertOperator Reference)
    native * (embedding * density * embedding.conjTranspose) * native.conjTranspose =
      embedding * (source * density * source.conjTranspose) * embedding.conjTranspose := by
  exact ControlKraus.conjugation_intertwines
    (R := (CleanSubspace.physical m ell width).prod Reference)
    (S := (CleanSubspace.carrier m ell modulus.val).prod Reference)
    (BasisEmbedding.withReference
      (CleanSubspace.embedding m ell width modulus.val nontrivial fits) Reference)
    (UnitaryOperator.prodTensor
      ((compiledGroupActionProgram m ell width modulus.val generator target).matrix environment)
      (1 : UnitaryOperator Reference)).val
    (orderedSource modulus m ell generator target ⊗ₖ (1 : HilbertOperator Reference))
    (actual_group_ordered_reference modulus m ell nontrivial fits generator target Reference)
    density

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordAction
