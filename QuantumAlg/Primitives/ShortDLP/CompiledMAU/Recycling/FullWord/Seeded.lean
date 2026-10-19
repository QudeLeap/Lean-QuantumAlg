/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Readout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Runtime
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Circuit
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Measurement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.FullWord.Extraction
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.MemberInstrument
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Preparation.Semantics
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Invariant
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Placement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Source
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Bank
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Reload
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.ParameterLayout
import all QuantumAlg.Components.Encoded.StateEmbedding
import all QuantumAlg.Core.Execution.Basis.Reference
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Store.Blocks
import all QuantumAlg.Core.Execution.Reindex
import all QuantumAlg.Core.Base.State.Density
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Actual old preparation supplies the complete stored partner/reference posterior

The reference density of each complete
actual Store is obtained from the real prepared state. The existing certified
basis target adjoins its unit-partner seed only as a mathematical comparison.
It is not an extra physical preparation, a supplied state certificate, or a
replacement for the actual zero allocation and literal X loader.

The final theorem executes that original preparation followed by the actual
selected compiled member, both Z readouts and the existing paid packing. It
keeps every old physical bank row, prior Store cell and reference coherence.
Reset/reload, new-context paid output correspondence, retry PMF and Solves
remain separate downstream obligations.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordSeeded

noncomputable section

variable {environment : RuntimeRound.model.Environment}

open Execution
open QuantumFourierTransform.Semiclassical (frequencyBits)
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma tensor_seed_entry {Source Target Reference : Register}
    (operator : Matrix Target.Index Source.Index ℂ) (seed : Source.Index)
    (reference : DensityOperator Reference) (left right : Target.Index)
    (leftRef rightRef : Reference.Index) :
    let kraus : Matrix (Target.prod Reference).Index (Source.prod Reference).Index ℂ :=
      operator ⊗ₖ (1 : HilbertOperator Reference)
    (kraus * (BasisReference.target seed reference).matrix * kraus.conjTranspose)
        (left, leftRef) (right, rightRef) =
      operator left seed * reference.matrix leftRef rightRef * star (operator right seed) := by
  let kraus : Matrix (Target.prod Reference).Index (Source.prod Reference).Index ℂ :=
    operator ⊗ₖ (1 : HilbertOperator Reference)
  let density : Matrix (Source.prod Reference).Index (Source.prod Reference).Index ℂ :=
    (BasisReference.target seed reference).matrix
  change (kraus * density * kraus.conjTranspose) (left, leftRef) (right, rightRef) = _
  have block :
      (kraus * density * kraus.conjTranspose) (left, leftRef) (right, rightRef) =
        (operator * density.submatrix
          (fun index => (index, leftRef)) (fun index => (index, rightRef)) *
          operator.conjTranspose) left right := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    change (∑ second : Source.Index × Reference.Index,
      (∑ first : Source.Index × Reference.Index,
        (operator left first.1 * (1 : HilbertOperator Reference) leftRef first.2) *
          density first second) *
        star (operator right second.1 *
          (1 : HilbertOperator Reference) rightRef second.2)) = _
    simp [Fintype.sum_prod_type, Matrix.one_apply, apply_ite]
  rw [block]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply,
    density, BasisReference.target_entry, ite_and, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)
  (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]

/-- A certified unit seed tensor the complete reference density of this actual stored block. -/
def seedDensity {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx) :
    DensityOperator ((Carrier.units modulus.val).prod Reference) :=
  BasisReference.target (1 : (Carrier.units modulus.val).Index)
    (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal

omit [NeZero modulus.val] in
private lemma referenceDensity_entry {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (seeded : RuntimeRound.HasSeedBlocks m ell width sameWires modulus.val state)
    (original : Store ctx) (leftRef rightRef : Reference.Index) :
    (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
        leftRef rightRef =
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (reloadLabel m ell width modulus.val), leftRef)
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (reloadLabel m ell width modulus.val), rightRef) := by
  change (DensityOperator.marginalLeft
    (DensityOperator.reindex (S := Reference.prod ctx.register)
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal
      (Equiv.prodComm ctx.register.Index Reference.Index))).matrix leftRef rightRef = _
  rw [DensityOperator.marginalLeft_matrix]
  simp only [DensityOperator.reindex_entry]
  exact BasisSeeded.reference_entry _ state seeded original leftRef rightRef

variable (nontrivial : 1 < modulus.val) (fits : modulus.val < 2 ^ width)

/-- The old physical measured bank surrounds the actual complete common-reference sigma. -/
def posterior {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx)
    (generator target : (ZMod modulus.val)ˣ)
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    HilbertOperator (ctx.register.prod Reference) :=
  let embedding := BasisEmbedding.matrix (BasisEmbedding.withReference
    (FullWordRuntime.outputEmbedding m ell width sameWires modulus nontrivial fits
      first second) Reference)
  embedding * FullWordCircuit.actualSigma (environment := environment.quantum) m ell width modulus
    generator target first second
    Reference (seedDensity width modulus state original).matrix * embedding.conjTranspose

/-- The comparison uses the same sigma and the reference density of the actual old block. -/
lemma posterior_eq_memberSigma
    (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx)
    (generator target : (ZMod modulus.val)ˣ)
    (recycledOriginal : Store (context base noQuantum m ell width))
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    posterior (environment := environment) m ell width sameWires modulus nontrivial fits state
      original generator target
        first second =
      let embedding := BasisEmbedding.matrix (BasisEmbedding.withReference
        (FullWordRuntime.outputEmbedding m ell width sameWires modulus nontrivial fits
          first second) Reference)
      embedding * MemberInstrument.memberSigma base noQuantum m ell width modulus generator target
        Reference recycledOriginal (frequencyBits (ell + m) first, frequencyBits ell second)
          (seedDensity width modulus state original).matrix * embedding.conjTranspose := by
  unfold posterior
  rw [FullWordCircuit.actualSigma_eq_memberSigma m ell width modulus nontrivial fits
    base noQuantum generator target Reference recycledOriginal first second]

private lemma unitary_entry_posterior {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (seeded : RuntimeRound.HasSeedBlocks m ell width sameWires modulus.val state)
    (original : Store ctx) (generator target : (ZMod modulus.val)ˣ)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index)
    (same : FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width sameWires left) =
      FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width sameWires right)) :
    (DensityOperator.applyUnitary
      (UnitaryOperator.prodTensor
        ((RuntimePlacement.memberProgram m ell width sameWires modulus.val generator target).matrix
          environment.quantum)
        (1 : UnitaryOperator Reference))
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal).matrix
        (left, leftRef) (right, rightRef) =
      posterior (environment := environment) m ell width sameWires modulus nontrivial fits state
        original generator target
        (FullWordExtraction.frequency m ell width
          (RuntimePlacement.basisEquiv m ell width sameWires left)).1
        (FullWordExtraction.frequency m ell width
          (RuntimePlacement.basisEquiv m ell width sameWires left)).2
        (left, leftRef) (right, rightRef) := by
  let outcome := FullWordExtraction.frequency m ell width
    (RuntimePlacement.basisEquiv m ell width sameWires left)
  have first : FullWordExtraction.frequency m ell width
      (RuntimePlacement.basisEquiv m ell width sameWires left) =
      (outcome.1, outcome.2) := rfl
  have second : FullWordExtraction.frequency m ell width
      (RuntimePlacement.basisEquiv m ell width sameWires right) =
      (outcome.1, outcome.2) := same.symm
  have branch := tensor_seed_entry
    (FullWordRuntime.conditionalColumns (environment := environment.quantum) m ell width sameWires
      modulus generator target
      outcome.1 outcome.2) (1 : (Carrier.units modulus.val).Index)
    (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal
    left right leftRef rightRef
  change FullWordRuntime.conditionalState (environment := environment.quantum) m ell width
    sameWires modulus generator target
      outcome.1 outcome.2 Reference (seedDensity width modulus state original).matrix
        (left, leftRef) (right, rightRef) = _ at branch
  rw [FullWordRuntime.conditionalState_factor m ell width sameWires modulus nontrivial fits]
    at branch
  simp only [FullWordRuntime.conditionalColumns, if_pos first, if_pos second] at branch
  rw [referenceDensity_entry m ell width sameWires modulus state seeded] at branch
  have actual := BasisSeeded.unitary_entry
    ((RuntimePlacement.basisEquiv m ell width sameWires).symm
      (reloadLabel m ell width modulus.val)) state seeded
    ((RuntimePlacement.memberProgram m ell width sameWires modulus.val generator target).matrix
      environment.quantum)
    original left right leftRef rightRef
  exact actual.trans branch.symm

private lemma seeded_store_entry {shape : CShape}
    (parameter : CInputRef ctx shape) (generator target : shape.Value → (ZMod modulus.val)ˣ)
    (cells : Fin (RuntimeRound.resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (RuntimeRound.resultBits m ell width)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (RuntimeRound.model.HiddenState × History))
    (seeded : RuntimeRound.HasSeedBlocks m ell width sameWires modulus.val state)
    (stored : Store ctx) (left right : ctx.register.Index)
    (leftRef rightRef : Reference.Index) :
    (((FullWordMeasurement.selectedMeasuredPacking m ell width sameWires parameter modulus.val
      generator target cells result).execute environment Reference state).filterClassical
        (fun entry => entry.1 = stored)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      let first := FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width sameWires left)
      let second := FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width sameWires right)
      if first = second then
        ∑ original : Store ctx,
          if FullWordReadout.frequencyStore m ell width sameWires cells result original
              first.1 first.2 = stored then
            posterior (environment := environment) m ell width sameWires modulus nontrivial fits
              state original
              (generator (original.read parameter)) (target (original.read parameter))
              first.1 first.2 (left, leftRef) (right, rightRef)
          else 0
      else 0 := by
  rw [FullWordReadout.selectedMeasuredPacking_frequency_store_entry]
  dsimp only
  split_ifs with same
  · apply Finset.sum_congr rfl
    intro original _
    split_ifs with reached
    · exact unitary_entry_posterior m ell width sameWires modulus nontrivial fits
        state seeded original (generator (original.read parameter))
        (target (original.read parameter)) left right leftRef rightRef same
    · rfl
  · rfl

section Prepared

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])

private abbrev Bank := RuntimeBank.context base noQuantum m ell width

private abbrev wires := RuntimeBank.shortDLP_runtimeBank_quantumWires
  base noQuantum m ell width

/-- Exactly the original allocation/loading followed by the actual measured and paid prefix. -/
def preparedCode {shape : CShape} (parameter : CInputRef (Bank m ell width base noQuantum) shape)
    (generator target : shape.Value → (ZMod modulus.val)ˣ)
    (cells : Fin (RuntimeRound.resultBits m ell width) →
      CWriteRef (Bank m ell width base noQuantum) (.finite 2))
    (result : CWriteRef (Bank m ell width base noQuantum)
      (.bits (RuntimeRound.resultBits m ell width))) :
    Circuit RuntimeRound.model base (Bank m ell width base noQuantum) :=
  (RuntimeBank.prepare (operations := BitWord.model) (services := .empty)
    base noQuantum m ell width modulus.val).seq
      (FullWordMeasurement.selectedMeasuredPacking m ell width (wires m ell width base noQuantum)
        parameter modulus.val generator target cells result)

/-- Actual initialization supplies sigma's reference density without any external seed premise. -/
lemma preparedCode_store_entry {shape : CShape}
    (parameter : CInputRef (Bank m ell width base noQuantum) shape)
    (generator target : shape.Value → (ZMod modulus.val)ˣ)
    (cells : Fin (RuntimeRound.resultBits m ell width) →
      CWriteRef (Bank m ell width base noQuantum) (.finite 2))
    (result : CWriteRef (Bank m ell width base noQuantum)
      (.bits (RuntimeRound.resultBits m ell width)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State base Reference (RuntimeRound.model.HiddenState × History))
    (stored : Store (Bank m ell width base noQuantum))
    (left right : (Bank m ell width base noQuantum).register.Index)
    (leftRef rightRef : Reference.Index) :
    (((preparedCode m ell width modulus base noQuantum parameter generator target cells
      result).execute environment Reference state).filterClassical
        (fun entry => entry.1 = stored)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      let initialized := (RuntimeBank.prepare (operations := BitWord.model) (services := .empty)
        base noQuantum m ell width modulus.val).execute environment Reference state
      let first := FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width (wires m ell width base noQuantum) left)
      let second := FullWordExtraction.frequency m ell width
        (RuntimePlacement.basisEquiv m ell width (wires m ell width base noQuantum) right)
      if first = second then
        ∑ original : Store (Bank m ell width base noQuantum),
          if FullWordReadout.frequencyStore m ell width (wires m ell width base noQuantum)
              cells result original first.1 first.2 = stored then
            posterior (environment := environment) m ell width (wires m ell width base noQuantum)
              modulus nontrivial fits
              initialized original (generator (original.read parameter))
              (target (original.read parameter)) first.1 first.2 (left, leftRef) (right, rightRef)
          else 0
      else 0 := by
  have composed := congrArg
    (fun density : DensityOperator ((Bank m ell width base noQuantum).register.prod Reference) =>
      density.matrix (left, leftRef) (right, rightRef))
    (Circuit.seq_store_marginal (environment := environment)
      (RuntimeBank.prepare (operations := BitWord.model) (services := .empty)
        base noQuantum m ell width modulus.val)
      (FullWordMeasurement.selectedMeasuredPacking m ell width (wires m ell width base noQuantum)
        parameter modulus.val generator target cells result) state stored)
  refine composed.trans ?_
  exact seeded_store_entry m ell width (wires m ell width base noQuantum) modulus nontrivial fits
    parameter generator target cells result _
    (RuntimeBank.shortDLP_runtimePrepare_seedBlocks base noQuantum m ell width modulus.val state)
    stored left right leftRef rightRef

end Prepared

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.FullWordSeeded
