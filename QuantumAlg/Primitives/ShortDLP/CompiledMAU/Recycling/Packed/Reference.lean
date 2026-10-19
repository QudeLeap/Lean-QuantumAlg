/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Packed.Instrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Packed.Frequency
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Context
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Packing
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Reload
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.MemberInstrument
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Seeded.Born
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Measurement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Seeded
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Clean.Stage
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Placement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Primitives.ShortDLP.Measurement
import all QuantumAlg.Components.Encoded.StateEmbedding.Reference
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Measurement.Fibers
import all QuantumAlg.Core.Execution.Measurement.Matrix
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency

/-!
# Actual packed member's complete stored-reference transition

The sampled native member and paid classical packing induce the source Born
kernel on each complete Store and every reference matrix entry. Incoming
store/history correlations and collisions of real writes remain in the sums.
The real reset and reload preserve this kernel and internally establish the
seed for the next member. The complete partner posterior is retained by the
separate instrument theorem; this statement contracts only that partner.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.PackedReference

noncomputable section

variable {environment : model.Environment}

open Execution QuantumFourierTransform.Semiclassical
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Decode the chronological outcome into the source's canonical frequency pair. -/
def frequencies (outcome : Bits (ell + m) × Bits ell) :
    Fin (2 ^ (ell + m)) × Fin (2 ^ ell) :=
  (qftReverseBits (ell + m) (binaryEquiv (ell + m) outcome.1),
    qftReverseBits ell (binaryEquiv ell outcome.2))

/-- The unchanged source Born mass of the actual chronological outcome. -/
def outcomeWeight (modulus : Fin (2 ^ width + 1))
    (generator target : (ZMod modulus.val)ˣ) (outcome : Bits (ell + m) × Bits ell) : ℝ :=
  ((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
    (CompiledMAU.evolvedState m ell width modulus.val generator target)
    (SeededBorn.sourceOutcome m ell width (frequencies m ell outcome).1
      (frequencies m ell outcome).2)).toReal

/-- This is the actual complete Store after measured member writes and the charged pack. -/
def packedStore
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    (original : Store (Context base noQuantum m ell width))
    (outcome : Bits (ell + m) × Bits ell) : Store (Context base noQuantum m ell width) :=
  (MemberInstrument.memberStore base noQuantum m ell width original outcome).applyOp
    (Packing.operation base noQuantum m ell width result)

/-- Weighted local traces group by complete stores without changing any reference entry. -/
private lemma weighted_store_reference {ctx : RuntimeCtx .quantum}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (weight : Store ctx → ℂ)
    (left right : Reference.Index) :
    ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) left right =
      ∑ original : Store ctx, weight original *
        ∑ basis : ctx.register.Index,
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, left) (basis, right) := by
  change (∑ basis : ctx.register.Index,
    ExecutionState.weightedMatrixEntry state (fun entry => weight entry.1)
      (basis, left) (basis, right)) = _
  simp_rw [FullWordMeasurement.weighted_store]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]

variable (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]
  (nontrivial : 1 < modulus.val) (fits : modulus.val < 2 ^ width)

include nontrivial fits in
/-- Contracting the exact chronological posterior gives its actual compiled Born mass. -/
private lemma member_reference_entry
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference History)
    (original : Store (Context base noQuantum m ell width))
    (generator target : (ZMod modulus.val)ˣ) (outcome : Bits (ell + m) × Bits ell)
    (left right : Reference.Index) :
    (∑ value : (Carrier.units modulus.val).Index,
      MemberInstrument.memberSigma base noQuantum m ell width modulus generator target Reference
        original outcome (FullWordSeeded.seedDensity width modulus state original).matrix
          (value, left) (value, right)) =
      (outcomeWeight m ell width modulus generator target outcome : ℂ) *
        (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
          left right := by
  have decoded :
      (frequencyBits (ell + m) (frequencies m ell outcome).1,
        frequencyBits ell (frequencies m ell outcome).2) = outcome :=
    Prod.ext (Partner.qftPartner_frequencyBits_decode (ell + m) outcome.1)
      (Partner.qftPartner_frequencyBits_decode ell outcome.2)
  conv_lhs => rw [← decoded]
  rw [← FullWordCircuit.actualSigma_eq_memberSigma
    (environment := OracleModel.emptyInterpretation) m ell width modulus
    nontrivial fits base noQuantum generator target Reference original]
  exact SeededBorn.actualSigma_reference_eq_compiled
    (environment := OracleModel.emptyInterpretation) m ell width modulus state original
    nontrivial fits generator target _ _ left right

include nontrivial fits in
/-- The actual packed complete-store block has the source mass on both reference indices. -/
lemma sampled_store_reference
    {shape : CShape} (parameter : CInputRef (Context base noQuantum m ell width) shape)
    (generator target : shape.Value → (ZMod modulus.val)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (Reload.seed base noQuantum m ell width modulus.val) state)
    (stored : Store (Context base noQuantum m ell width)) (left right : Reference.Index) :
    (∑ basis : (Context base noQuantum m ell width).register.Index,
      (((Round.sampled base noQuantum m ell width parameter modulus.val generator
        target result).execute environment Reference state).filterClassical
          (fun entry => entry.1 = stored)).quantumMarginal.matrix (basis, left) (basis, right)) =
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          if packedStore base noQuantum m ell width result original outcome = stored then
            (outcomeWeight m ell width modulus (generator (original.read parameter))
              (target (original.read parameter)) outcome : ℂ) *
                (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
                  left right
          else 0 := by
  rw [PackedInstrument.seeded_sampled_store_matrix base noQuantum m ell width modulus
    (Nat.zero_lt_of_lt nontrivial) parameter generator target result state seeded stored]
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  by_cases reached : packedStore base noQuantum m ell width result original outcome = stored
  · simp only [packedStore] at reached
    simp only [packedStore, reached, if_true]
    rw [CleanStage.zeroEmbedding, BasisEmbedding.reference_sandwich_sum]
    exact member_reference_entry base noQuantum m ell width modulus nontrivial fits
      state original (generator (original.read parameter)) (target (original.read parameter))
        outcome left right
  · simp only [packedStore] at reached
    simp only [packedStore, reached, if_false, Finset.sum_const_zero]

include nontrivial fits in
/-- Every store-weighted reference block follows the same actual sampled source transition. -/
lemma sampled_referenceFiberSum
    {shape : CShape} (parameter : CInputRef (Context base noQuantum m ell width) shape)
    (generator target : shape.Value → (ZMod modulus.val)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (Reload.seed base noQuantum m ell width modulus.val) state)
    (weight : Store (Context base noQuantum m ell width) → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Round.sampled base noQuantum m ell width parameter modulus.val generator
        target result).execute environment Reference state) (fun entry _ => weight entry.1) left
          right =
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          weight (packedStore base noQuantum m ell width result original outcome) *
            (outcomeWeight m ell width modulus (generator (original.read parameter))
              (target (original.read parameter)) outcome : ℂ) *
                (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
                  left right := by
  rw [weighted_store_reference]
  simp_rw [sampled_store_reference base noQuantum m ell width modulus nontrivial fits
    parameter generator target result state seeded]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outcome _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact (mul_assoc _ _ _).symm

include nontrivial fits in
/-- The complete reset/reload round preserves the kernel used by the next actual member. -/
lemma round_referenceFiberSum
    {shape : CShape} (parameter : CInputRef (Context base noQuantum m ell width) shape)
    (generator target : shape.Value → (ZMod modulus.val)ˣ)
    (result : CWriteRef (Context base noQuantum m ell width) (.bits (resultBits m ell)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (Reload.seed base noQuantum m ell width modulus.val) state)
    (weight : Store (Context base noQuantum m ell width) → ℂ) (left right : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((Round.code base noQuantum m ell width parameter modulus.val generator
        target result).execute environment Reference state) (fun entry _ => weight entry.1) left
          right =
      ∑ original : Store (Context base noQuantum m ell width),
        ∑ outcome : Bits (ell + m) × Bits ell,
          weight (packedStore base noQuantum m ell width result original outcome) *
            (outcomeWeight m ell width modulus (generator (original.read parameter))
              (target (original.read parameter)) outcome : ℂ) *
                (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
                  left right := by
  rw [Round.code_referenceFiberSum_afterPack]
  exact sampled_referenceFiberSum base noQuantum m ell width modulus nontrivial fits
    parameter generator target result state seeded weight left right

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.PackedReference
