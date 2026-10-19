/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Stages
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Action
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.PartnerComparison
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.MemberInstrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Stages
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Group.Action
import all QuantumAlg.Primitives.ShortDLP.Layout
import all QuantumAlg.Primitives.ShortDLP.Oracle.Mathematics
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Phases
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Permutation
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Extracting the old actual compiled member's complete clean-partner Kraus

Every old amplitude below is an entry of
the actual compiledCircuit: native Hadamards, both real full-word modular
exponentiation programs on their shared arithmetic words, and both complete
native inverse QFTs. The exact columns cover arbitrary clean unit partners,
not merely the seed-one source vector. Their measured-frequency Kraus is then
identified with the existing shared QFT contraction and the real stored
recycling trajectory. Actual physical placement and measurement execution
remain separate downstream bridges; unequal full registers are not equated.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordCircuit

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open QuantumFourierTransform.Semiclassical
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

section CompiledColumn

variable (m ell width N : Nat) [NeZero N] (nontrivial : 1 < N) (fits : N < 2 ^ width)

include nontrivial fits in
omit [NeZero N] in
/-- Every output amplitude comes from the actual compiled stages and their clean ket action. -/
lemma compiled_column (generator target : (ZMod N)ˣ) (seed : (ZMod N)ˣ)
    (output : Fin (2 ^ totalQubits (registerParameters m ell width))) :
    ((compiledCircuit m ell width N generator target).binaryMatrix environment) output
        (cleanLabel m ell width N 0 0 seed) =
      ∑ first : Fin (2 ^ (ell + m)), ∑ second : Fin (2 ^ ell),
        (NormalizedVector.invSqrt2 ^ (ell + m) * NormalizedVector.invSqrt2 ^ ell) *
          ((readoutCircuit (registerParameters m ell width)).binaryMatrix environment) output
            (cleanLabel m ell width N first second
              (oracleValue generator target first.val second.val * seed)) := by
  let preparation : UnitaryOperator (Qubits (totalQubits (registerParameters m ell width))) :=
    ((preparationCircuit (registerParameters m ell width)).binaryMatrix environment)
  let group : UnitaryOperator (Qubits (totalQubits (registerParameters m ell width))) :=
    ((compiledGroupActionProgram m ell width N generator target).binaryMatrix environment)
  let readout : UnitaryOperator (Qubits (totalQubits (registerParameters m ell width))) :=
    ((readoutCircuit (registerParameters m ell width)).binaryMatrix environment)
  have outer := UnitaryCircuit.unitaryCircuit_binaryMatrix_seq
    (environment := environment)
    (preparationCircuit (registerParameters m ell width))
    ((compiledGroupActionProgram m ell width N generator target).seq
      (readoutCircuit (registerParameters m ell width)))
  have inner : (((compiledGroupActionProgram m ell width N generator target).seq
      (readoutCircuit (registerParameters m ell width))).binaryMatrix environment) = readout *
        group :=
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq (environment := environment)
      (compiledGroupActionProgram m ell width N generator target)
      (readoutCircuit (registerParameters m ell width))
  have matrices : ((compiledCircuit m ell width N generator target).binaryMatrix environment) =
      readout * group * preparation :=
    outer.trans (congrArg
      (fun operator : UnitaryOperator (Qubits (totalQubits (registerParameters m ell width))) =>
        operator * preparation) inner)
  refine (congrArg
    (fun operator : UnitaryOperator (Qubits (totalQubits (registerParameters m ell width))) =>
      operator output (cleanLabel m ell width N 0 0 seed)) matrices).trans ?_
  change ((readout : HilbertOperator
      (Qubits (totalQubits (registerParameters m ell width)))) *
    (group : HilbertOperator (Qubits (totalQubits (registerParameters m ell width)))) *
    (preparation : HilbertOperator (Qubits (totalQubits (registerParameters m ell width)))))
      output (cleanLabel m ell width N 0 0 seed) = _
  rw [Matrix.mul_apply]
  rw [← Equiv.sum_comp (tripleEquiv (registerParameters m ell width))]
  simp only [Fintype.sum_prod_type, tripleEquiv, Equiv.trans_apply, Equiv.prodCongr_apply]
  change (∑ first : Fin (2 ^ (ell + m)), ∑ second : Fin (2 ^ ell),
    ∑ workspace : Fin (2 ^ workspaceBits width),
      ((readout : HilbertOperator (Qubits (totalQubits (registerParameters m ell width)))) *
        (group : HilbertOperator (Qubits (totalQubits (registerParameters m ell width)))))
          output (tripleIndex (registerParameters m ell width) first second workspace) *
        (preparation : HilbertOperator
          (Qubits (totalQubits (registerParameters m ell width))))
          (tripleIndex (registerParameters m ell width) first second workspace)
          (tripleIndex (registerParameters m ell width) 0 0 (cleanUnitLabel width N seed))) = _
  dsimp only [preparation]
  simp_rw [FullWordStages.preparation_column, FullWordStages.normalization]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  change ((readout : HilbertOperator
      (Qubits (totalQubits (registerParameters m ell width)))) *
    (group : HilbertOperator (Qubits (totalQubits (registerParameters m ell width)))))
      output (cleanLabel m ell width N first second seed) * _ = _
  dsimp only [group]
  simp_rw [Matrix.mul_apply,
    FullWordStages.group_clean_column m ell width N nontrivial fits generator target]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  dsimp only [readout]
  simp only [firstBits, registerParameters]
  ring

end CompiledColumn

variable {width : Nat}

/-- The shared complete native Fourier contraction at the original full exponent labels. -/
lemma fullOldKraus_sum (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]
    (bits : Nat) (unit : (ZMod modulus.val)ˣ) (frequency : Fin (2 ^ bits)) :
    Partner.fullOldKraus true bits
        (fun position => (PartnerComparison.powerOperators modulus bits unit position :
          HilbertOperator (Carrier.units modulus.val))) frequency =
      ∑ input : Fin (2 ^ bits),
        (Partner.fullRows true bits frequency ((binaryEquiv bits).symm input) *
          NormalizedVector.invSqrt2 ^ bits) •
            (Carrier.translation modulus (unit ^ input.val) :
              HilbertOperator (Carrier.units modulus.val)) := by
  rw [Partner.qftPartner_fullOldKraus_physical, Partner.qftPartner_oldKraus_contraction]
  simp only [Partner.contraction, Partner.phaseBasis_one, mul_one]
  simp_rw [FullWordAction.orderedWord_power]
  rw [← Equiv.sum_comp (binaryEquiv bits).symm]
  simp only [Equiv.apply_symm_apply]
  simp_rw [← Partner.qftPartner_fullRows_physical]

variable (m ell width : Nat) (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]

/-- This operator is extracted from the actual compiled circuit, not prescribed by the source. -/
def actualKraus (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    HilbertOperator (Carrier.units modulus.val) :=
  fun row column =>
    ((compiledCircuit m ell width modulus.val generator target).binaryMatrix environment)
      (cleanLabel m ell width modulus.val first second row)
      (cleanLabel m ell width modulus.val 0 0 column)

variable (nontrivial : 1 < modulus.val) (fits : modulus.val < 2 ^ width)

include nontrivial fits in
/-- Both actual inverse-QFT output frequencies select the product on the same clean partner. -/
lemma actualKraus_eq_shared (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    actualKraus (environment := environment) m ell width modulus generator target first second =
      Partner.fullOldKraus true ell
        (fun position => (PartnerComparison.powerOperators modulus ell target⁻¹ position :
          HilbertOperator (Carrier.units modulus.val))) second *
        Partner.fullOldKraus true (ell + m)
          (fun position => (PartnerComparison.powerOperators modulus (ell + m)
            generator position : HilbertOperator (Carrier.units modulus.val))) first := by
  let firstAmplitude (input : Fin (2 ^ (ell + m))) : ℂ :=
    Partner.fullRows true (ell + m) first ((binaryEquiv (ell + m)).symm input)
  let secondAmplitude (input : Fin (2 ^ ell)) : ℂ :=
    Partner.fullRows true ell second ((binaryEquiv ell).symm input)
  let firstWeight (input : Fin (2 ^ (ell + m))) : ℂ :=
    firstAmplitude input * NormalizedVector.invSqrt2 ^ (ell + m)
  let secondWeight (input : Fin (2 ^ ell)) : ℂ :=
    secondAmplitude input * NormalizedVector.invSqrt2 ^ ell
  have expanded :
      Partner.fullOldKraus true ell
          (fun position => (PartnerComparison.powerOperators modulus ell target⁻¹ position :
            HilbertOperator (Carrier.units modulus.val))) second *
        Partner.fullOldKraus true (ell + m)
          (fun position => (PartnerComparison.powerOperators modulus (ell + m)
            generator position : HilbertOperator (Carrier.units modulus.val))) first =
      ∑ sourceFirst : Fin (2 ^ (ell + m)), ∑ sourceSecond : Fin (2 ^ ell),
        (secondWeight sourceSecond * firstWeight sourceFirst) •
          (Carrier.translation modulus
            (target⁻¹ ^ sourceSecond.val * generator ^ sourceFirst.val) :
              HilbertOperator (Carrier.units modulus.val)) := by
    rw [fullOldKraus_sum, fullOldKraus_sum]
    change
      (∑ input : Fin (2 ^ ell), secondWeight input •
        (Carrier.translation modulus (target⁻¹ ^ input.val) :
          HilbertOperator (Carrier.units modulus.val))) *
      (∑ input : Fin (2 ^ (ell + m)), firstWeight input •
        (Carrier.translation modulus (generator ^ input.val) :
          HilbertOperator (Carrier.units modulus.val))) = _
    simp only [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    apply Finset.sum_congr rfl
    intro sourceFirst _
    apply Finset.sum_congr rfl
    intro sourceSecond _
    rw [mul_comm (firstWeight sourceFirst) (secondWeight sourceSecond)]
    exact congrArg
      (fun operator : HilbertOperator (Carrier.units modulus.val) =>
        (secondWeight sourceSecond * firstWeight sourceFirst) • operator)
      (FullWordAction.translation_mul modulus
        (target⁻¹ ^ sourceSecond.val) (generator ^ sourceFirst.val))
  refine Eq.trans ?_ expanded.symm
  ext row column
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine (compiled_column m ell width modulus.val nontrivial fits generator target column
    (cleanLabel m ell width modulus.val first second row)).trans ?_
  apply Finset.sum_congr rfl
  intro sourceFirst _
  apply Finset.sum_congr rfl
  intro sourceSecond _
  have readout :
      ((readoutCircuit (registerParameters m ell width)).binaryMatrix environment)
          (cleanLabel m ell width modulus.val first second row)
          (cleanLabel m ell width modulus.val sourceFirst sourceSecond
            (oracleValue generator target sourceFirst.val sourceSecond.val * column)) =
      firstAmplitude sourceFirst * secondAmplitude sourceSecond *
        (if row = oracleValue generator target sourceFirst.val sourceSecond.val * column
          then 1 else 0) :=
    FullWordStages.readout_clean_entry m ell width modulus.val nontrivial fits
      first sourceFirst second sourceSecond row
      (oracleValue generator target sourceFirst.val sourceSecond.val * column)
  have coefficient : target⁻¹ ^ sourceSecond.val * generator ^ sourceFirst.val =
      oracleValue generator target sourceFirst.val sourceSecond.val := by
    simp only [oracleValue, inv_pow]
    ac_rfl
  have translationEntry :
      (Carrier.translation modulus
        (target⁻¹ ^ sourceSecond.val * generator ^ sourceFirst.val) :
          HilbertOperator (Carrier.units modulus.val)) row column =
      (if row = oracleValue generator target sourceFirst.val sourceSecond.val * column
        then (1 : ℂ) else 0) := by
    simp only [Carrier.translation, UnitaryOperator.ofPerm_entry,
      Equiv.mulLeft_symm_apply, coefficient, inv_mul_eq_iff_eq_mul]
  calc
    _ = (NormalizedVector.invSqrt2 ^ (ell + m) * NormalizedVector.invSqrt2 ^ ell) *
        (firstAmplitude sourceFirst * secondAmplitude sourceSecond *
          (if row = oracleValue generator target sourceFirst.val sourceSecond.val * column
            then 1 else 0)) :=
      congrArg (fun value : ℂ =>
        (NormalizedVector.invSqrt2 ^ (ell + m) * NormalizedVector.invSqrt2 ^ ell) * value) readout
    _ = (secondWeight sourceSecond * firstWeight sourceFirst) *
        (if row = oracleValue generator target sourceFirst.val sourceSecond.val * column
          then 1 else 0) := by
      dsimp only [firstWeight, secondWeight]
      ring
    _ = _ := congrArg
      (fun value : ℂ => (secondWeight sourceSecond * firstWeight sourceFirst) * value)
      translationEntry.symm

/-- The complete actual conditional partner/reference posterior has no purity restriction. -/
def actualSigma (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) (Reference : Register)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    HilbertOperator ((Carrier.units modulus.val).prod Reference) :=
  let kraus : HilbertOperator ((Carrier.units modulus.val).prod Reference) :=
    actualKraus (environment := environment) m ell width modulus generator target first second ⊗ₖ
      (1 : HilbertOperator Reference)
  kraus * density * kraus.conjTranspose

include nontrivial fits in
/-- The actual full-word circuit and stored recycled trajectory retain the same sigma_y. -/
lemma actualSigma_eq_memberSigma
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    (generator target : (ZMod modulus.val)ˣ) (Reference : Register)
    (original : Execution.Store (context base noQuantum m ell width))
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    actualSigma (environment := environment) m ell width modulus generator target first second
      Reference density =
      MemberInstrument.memberSigma base noQuantum m ell width modulus generator target Reference
        original (frequencyBits (ell + m) first, frequencyBits ell second) density := by
  rw [PartnerComparison.memberSigma_fullSigma, actualSigma,
    actualKraus_eq_shared m ell width modulus nontrivial fits]
  have tensor (left right : HilbertOperator (Carrier.units modulus.val)) :
      (left * right) ⊗ₖ (1 : HilbertOperator Reference) =
        (left ⊗ₖ (1 : HilbertOperator Reference)) *
          (right ⊗ₖ (1 : HilbertOperator Reference)) := by
    simpa only [Matrix.one_mul] using
      Matrix.mul_kronecker_mul left right
        (1 : HilbertOperator Reference) (1 : HilbertOperator Reference)
  let firstKraus : HilbertOperator ((Carrier.units modulus.val).prod Reference) :=
    Partner.fullOldKraus true (ell + m)
      (fun position => (PartnerComparison.powerOperators modulus (ell + m)
        generator position : HilbertOperator (Carrier.units modulus.val))) first ⊗ₖ
      (1 : HilbertOperator Reference)
  let secondKraus : HilbertOperator ((Carrier.units modulus.val).prod Reference) :=
    Partner.fullOldKraus true ell
      (fun position => (PartnerComparison.powerOperators modulus ell target⁻¹ position :
        HilbertOperator (Carrier.units modulus.val))) second ⊗ₖ
      (1 : HilbertOperator Reference)
  rw [tensor]
  change (secondKraus * firstKraus) * density *
      (secondKraus * firstKraus).conjTranspose =
    secondKraus * (firstKraus * density * firstKraus.conjTranspose) *
      secondKraus.conjTranspose
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordCircuit
