/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Source.Fibers
import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# Every observed actual round result retains its complete reference fiber

Summing the final local seed coordinates gives one on each complete store
block. A finite classical observation therefore reads precisely the actual
measured and packed fiber of the selected-member state. This holds for
arbitrary input correlations and arbitrary reference matrix coordinates.

The observation may retain the sampled parameter and all earlier results
alongside the newest packed result. It is a mathematical read of the actual
final store, not a new runtime instruction or a prescribed distribution.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

private lemma round_store_reference {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) (original : Store ctx)
    (leftRef rightRef : Reference.Index) :
    (∑ basis : ctx.register.Index,
      (ExecutionState.filterClassical
        ((code m ell width sameWires parameter N generator target cells result).execute environment
          Reference state) (fun entry => entry.1 = original)).quantumMarginal.matrix
            (basis, leftRef) (basis, rightRef)) =
      ExecutionState.referenceFiberSum
        ((selected m ell width sameWires parameter N generator target).execute
          environment Reference state)
        (fun entry basis =>
          if packedBasisStore m ell width sameWires cells result entry.1 basis = original
          then 1 else 0) leftRef rightRef := by
  let output := (code m ell width sameWires parameter N generator target cells result).execute
    environment
    Reference state
  let seed := (RuntimePlacement.basisEquiv m ell width sameWires).symm
    (CompiledMAU.reloadLabel m ell width N)
  have support := shortDLP_runtimeSeedBlocks_reference_entry m ell width sameWires N output
    (shortDLP_runtimeRound_seedBlocks m ell width sameWires parameter N generator target
      cells result state) original leftRef rightRef
  have entry := shortDLP_runtimeRound_store_reference_entry (environment := environment)
    m ell width sameWires parameter N
    generator target cells result state original seed seed leftRef rightRef
  refine support.trans (entry.trans ?_)
  let coefficient := ExecutionState.referenceFiberSum
    ((selected m ell width sameWires parameter N generator target).execute
      environment Reference state)
    (fun entry basis =>
      if packedBasisStore m ell width sameWires cells result entry.1 basis = original
      then 1 else 0) leftRef rightRef
  have atSeed : NormalizedVector.ket (R := ctx.register) seed seed = 1 :=
    (NormalizedVector.ket_apply seed seed).trans (if_pos rfl)
  change NormalizedVector.ket (R := ctx.register) seed seed * coefficient *
    star (NormalizedVector.ket (R := ctx.register) seed seed) = coefficient
  simp only [atSeed, one_mul, star_one, mul_one]

/-- Any scalar read of the actual final store has exactly the actual packed reference fiber. -/
lemma shortDLP_runtimeRound_referenceFiberSum {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) (weight : Store ctx → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code m ell width sameWires parameter N generator target cells result).execute environment
        Reference state)
      (fun entry _ => weight entry.1) leftRef rightRef =
      ExecutionState.referenceFiberSum
        ((selected m ell width sameWires parameter N generator target).execute
          environment Reference state)
        (fun entry basis =>
          weight (packedBasisStore m ell width sameWires cells result entry.1 basis))
        leftRef rightRef := by
  refine (BasisSeeded.fiber_store_blocks
    ((code m ell width sameWires parameter N generator target cells result).execute
      environment Reference state)
    (fun store _ => weight store) leftRef rightRef).trans ?_
  rw [Finset.sum_comm]
  have stores :
      (∑ original : Store ctx, ∑ basis : ctx.register.Index, weight original *
        (ExecutionState.filterClassical
          ((code m ell width sameWires parameter N generator target cells result).execute
            environment
            Reference state) (fun entry => entry.1 = original)).quantumMarginal.matrix
              (basis, leftRef) (basis, rightRef)) =
      ∑ original : Store ctx, weight original * ExecutionState.referenceFiberSum
        ((selected m ell width sameWires parameter N generator target).execute
          environment Reference state)
        (fun entry basis =>
          if packedBasisStore m ell width sameWires cells result entry.1 basis = original
          then 1 else 0) leftRef rightRef := by
    apply Finset.sum_congr rfl
    intro original _
    rw [← Finset.mul_sum]
    exact congrArg (fun value : ℂ => weight original * value)
      (round_store_reference m ell width sameWires parameter N generator target
        cells result state original leftRef rightRef)
  refine stores.trans ?_
  simp only [ExecutionState.referenceFiberSum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro basis _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro entry _
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Reading the actual outcome and earlier stored data retains every reference entry. -/
lemma shortDLP_runtimeRound_observed_reference_entry {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    {Reference : Register} {History Observed : Type} [Fintype History] [Fintype Observed]
    (state : State ctx Reference (model.HiddenState × History))
    (observe : Store ctx → Observed) (value : Observed)
    (leftRef rightRef : Reference.Index) :
    (∑ basis : ctx.register.Index,
      ((ExecutionState.mapClassical
        ((code m ell width sameWires parameter N generator target cells result).execute environment
          Reference state) (fun entry => observe entry.1)).block value).matrix
          (basis, leftRef) (basis, rightRef)) =
      ExecutionState.referenceFiberSum
        ((selected m ell width sameWires parameter N generator target).execute
          environment Reference state)
        (fun entry basis =>
          if observe (packedBasisStore m ell width sameWires cells result entry.1 basis) = value
          then 1 else 0) leftRef rightRef :=
  (ExecutionState.mapClassical_block_referenceFiberSum
    ((code m ell width sameWires parameter N generator target cells result).execute
      environment Reference state)
    (fun entry => observe entry.1) value leftRef rightRef).trans
    (shortDLP_runtimeRound_referenceFiberSum m ell width sameWires parameter N generator target
      cells result state (fun store => if observe store = value then 1 else 0) leftRef rightRef)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
