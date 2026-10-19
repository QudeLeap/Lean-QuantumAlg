/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Clean.Instrument

/-!
# Actual two-stream instrument with one persistent arithmetic accumulator

The real generator stream is followed by
the real inverse-target stream on the same physical bank and common arbitrary
Reference. Their actual Stores and complete unnormalized posteriors are passed
forward without reseeding. Every outcome remains in the actual retained cells;
possible Store collisions are summed, not discarded. No arbitrary dirty-input
arithmetic commutation, old-bank full-state equality, free packing, or caller
instrument certificate is asserted.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.MemberInstrument

noncomputable section

open Execution

variable {environment : model.Environment}
open QuantumFourierTransform.Semiclassical (Bits)
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The actual two complete chronological streams retain both vectors in the same Store. -/
def memberStore (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) : Store (Context base noQuantum m ell width) :=
  NativeInstrument.suffixStore base noQuantum m ell width true
    (secondCell base noQuantum m ell width) ell 0 (by omega)
    (NativeInstrument.suffixStore base noQuantum m ell width true
      (firstCell base noQuantum m ell width) (ell + m) 0 (by omega) original outcome.1) outcome.2

/-- Actual branch product, with the inverse-target prefix reading the completed first Store. -/
def memberKraus (N : Nat) (generator target : (ZMod N)ˣ) (Reference : Register)
    (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) :
    HilbertOperator ((Context base noQuantum m ell width).register.prod Reference) :=
  NativeInstrument.suffixKraus (environment := environment) base noQuantum m ell width true
    (secondCell base noQuantum m ell width) N target⁻¹ Reference ell 0 (by omega)
    (NativeInstrument.suffixStore base noQuantum m ell width true
      (firstCell base noQuantum m ell width) (ell + m) 0 (by omega) original outcome.1) outcome.2 *
  NativeInstrument.suffixKraus (environment := environment) base noQuantum m ell width true
    (firstCell base noQuantum m ell width) N generator Reference (ell + m) 0 (by omega)
      original outcome.1

/-- The literal member, for unrestricted dirty mixed input, derives its adaptive instrument. -/
lemma member_store_matrix (N : Nat) (generator target : (ZMod N)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (stored : Store (Context base noQuantum m ell width)) :
    ((member base noQuantum m ell width N generator target).execute environment Reference state
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          if memberStore base noQuantum m ell width original outcome = stored then
            let operator := memberKraus (environment := environment) base noQuantum m ell width N
              generator target Reference
              original outcome
            operator *
              (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
                operator.conjTranspose
          else 0 := by
  rw [member]
  refine (congrArg DensityOperator.matrix (Circuit.seq_store_marginal
    (exponentCode base noQuantum m ell width true (firstCell base noQuantum m ell width)
      N generator)
    (exponentCode base noQuantum m ell width true (secondCell base noQuantum m ell width)
      N target⁻¹) environment state stored)).trans ?_
  change ((exponentSuffix base noQuantum m ell width true (secondCell base noQuantum m ell width)
    N target⁻¹ ell 0 (by omega)).execute environment Reference
      ((exponentSuffix base noQuantum m ell width true (firstCell base noQuantum m ell width)
        N generator (ell + m) 0 (by omega)).execute environment Reference state)
    |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix = _
  rw [NativeInstrument.exponentSuffix_store_matrix]
  simp_rw [NativeInstrument.exponentSuffix_store_matrix]
  rw [NativeInstrument.storedConjugation_compose_selected]
  apply Finset.sum_congr rfl
  intro original _
  let contribution (outcome : Bits (ell + m) × Bits ell) :
      HilbertOperator ((Context base noQuantum m ell width).register.prod Reference) :=
    if memberStore base noQuantum m ell width original outcome = stored then
      let operator := memberKraus (environment := environment) base noQuantum m ell width N
        generator target Reference
        original outcome
      operator *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
          operator.conjTranspose
    else 0
  change (∑ first : Bits (ell + m), ∑ second : Bits ell, contribution (first, second)) =
    ∑ outcome : Bits (ell + m) × Bits ell, contribution outcome
  exact (Fintype.sum_prod_type contribution).symm

variable (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val] (positive : 0 < modulus.val)

/-- Both clean branch products act on the same accumulator/reference operator space. -/
def memberSourceKraus (generator target : (ZMod modulus.val)ˣ) (Reference : Register)
    (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) :
    HilbertOperator ((Carrier.units modulus.val).prod Reference) :=
  CleanInstrument.sourceSuffix base noQuantum m ell width modulus true
    (secondCell base noQuantum m ell width) target⁻¹ Reference ell 0 (by omega)
    (NativeInstrument.suffixStore base noQuantum m ell width true
      (firstCell base noQuantum m ell width) (ell + m) 0 (by omega) original outcome.1) outcome.2 *
  CleanInstrument.sourceSuffix base noQuantum m ell width modulus true
    (firstCell base noQuantum m ell width) generator Reference (ell + m) 0 (by omega)
      original outcome.1

/-- The complete first posterior is the input of the second exponent, with no new seed. -/
def memberSigma (generator target : (ZMod modulus.val)ˣ) (Reference : Register)
    (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    HilbertOperator ((Carrier.units modulus.val).prod Reference) :=
  CleanInstrument.sigmaSuffix base noQuantum m ell width modulus true
    (secondCell base noQuantum m ell width) target⁻¹ Reference ell 0 (by omega)
    (NativeInstrument.suffixStore base noQuantum m ell width true
      (firstCell base noQuantum m ell width) (ell + m) 0 (by omega) original outcome.1) outcome.2
    (CleanInstrument.sigmaSuffix base noQuantum m ell width modulus true
      (firstCell base noQuantum m ell width) generator Reference (ell + m) 0 (by omega)
        original outcome.1 density)

lemma memberSigma_eq_product (generator target : (ZMod modulus.val)ˣ) (Reference : Register)
    (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell)
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    memberSigma base noQuantum m ell width modulus generator target Reference original outcome
        density =
      memberSourceKraus base noQuantum m ell width modulus generator target Reference original
          outcome * density *
        (memberSourceKraus base noQuantum m ell width modulus generator target Reference original
          outcome).conjTranspose := by
  simp only [memberSigma, CleanInstrument.sigmaSuffix_eq_product, memberSourceKraus,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma memberKraus_intertwines (generator target : (ZMod modulus.val)ˣ) (Reference : Register)
    (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) :
    memberKraus (environment := environment) base noQuantum m ell width modulus.val generator
      target Reference original outcome *
      BasisEmbedding.matrix
        (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference) =
    BasisEmbedding.matrix
        (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference) *
      memberSourceKraus base noQuantum m ell width modulus generator target Reference original
        outcome := by
  rw [memberKraus, memberSourceKraus, Matrix.mul_assoc,
    CleanInstrument.suffixKraus_intertwines base noQuantum m ell width modulus positive]
  rw [← Matrix.mul_assoc,
    CleanInstrument.suffixKraus_intertwines base noQuantum m ell width modulus positive]
  simp only [Matrix.mul_assoc]

/-- The actual stored two-stream instrument is exactly the persistent common-reference posterior. -/
lemma member_clean_store_matrix (generator target : (ZMod modulus.val)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : ExecutionState (Store (Context base noQuantum m ell width) ×
      (model.HiddenState × History)) ((Carrier.units modulus.val).prod Reference))
    (stored : Store (Context base noQuantum m ell width)) :
    ((member base noQuantum m ell width modulus.val generator target).execute environment Reference
        (CleanStage.encodeState base noQuantum m ell width modulus positive state)
      |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          if memberStore base noQuantum m ell width original outcome = stored then
            let embedding := BasisEmbedding.matrix
              (CleanStage.zeroEmbedding base noQuantum m ell width modulus positive Reference)
            embedding *
              memberSigma base noQuantum m ell width modulus generator target Reference original
                outcome ((state.mapClassical (fun entry => entry.1)).block original).matrix *
              embedding.conjTranspose
          else 0 := by
  rw [member_store_matrix]
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro outcome _
  split_ifs with reached
  · rw [CleanInstrument.encodeState_store_matrix base noQuantum m ell width modulus positive]
    rw [memberSigma_eq_product]
    exact ControlKraus.conjugation_intertwines _ _ _
      (memberKraus_intertwines base noQuantum m ell width modulus positive generator target
        Reference original outcome)
      ((state.mapClassical (fun entry => entry.1)).block original).matrix
  · rfl

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.MemberInstrument
