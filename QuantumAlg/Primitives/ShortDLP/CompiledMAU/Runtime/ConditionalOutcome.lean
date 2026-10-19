/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.OutcomeFibers

/-!
# The actual round's conditional source kernel with all prior correlations

Observing the sampled parameter together with any earlier stored data fixes
the source member used by the actual unitary. The joint new-outcome reference
block is therefore the original source outcome probability multiplied by the
same earlier-data reference block of the actual input state. Off-diagonal
reference entries remain in the equality.

This statement is derived from the actual measured, packed and reset/reloaded
circuit. No independently sampled output, factorized input state or positive
probability premise is introduced. The internal seed and key facts are supplied
by the concrete allocation and repetition layout.
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

/-- A complete-store weight retains the actual seeded input's full reference coefficient. -/
lemma shortDLP_runtimeSeedBlocks_weighted_reference (N : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (seeded : HasSeedBlocks m ell width sameWires N state)
    (weight : Store ctx → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum state (fun entry _ => weight entry.1) leftRef rightRef =
      ∑ original : Store ctx, weight original *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          ((RuntimePlacement.basisEquiv m ell width sameWires).symm
            (CompiledMAU.reloadLabel m ell width N), leftRef)
          ((RuntimePlacement.basisEquiv m ell width sameWires).symm
            (CompiledMAU.reloadLabel m ell width N), rightRef) := by
  refine (BasisSeeded.fiber_store_blocks
    state (fun store _ => weight store) leftRef rightRef).trans ?_
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [← Finset.mul_sum]
  exact congrArg (fun value : ℂ => weight original * value)
    (shortDLP_runtimeSeedBlocks_reference_entry m ell width sameWires N state seeded
      original leftRef rightRef)

/-- The actual conditional outcome multiplies the unchanged earlier-data reference block. -/
lemma shortDLP_runtimeRound_conditional_outcome_reference
    {parameterShape previousShape : CShape}
    (parameter : CInputRef ctx parameterShape) (previous : CInputRef ctx previousShape)
    (N : Nat) (generator target : parameterShape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (distinct : Function.Injective (fun index => (cells index).key))
    (cellsSeparate : ∀ index, (cells index).key ∉
      (CInputRef.product parameter previous).storageKeys)
    (resultSeparate : result.key ∉ (CInputRef.product parameter previous).storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (seeded : HasSeedBlocks m ell width sameWires N state)
    (parameterValue : parameterShape.Value) (previousValue : previousShape.Value)
    (outcome : Fin (resultBits m ell width) → Bool) (leftRef rightRef : Reference.Index) :
    (∑ basis : ctx.register.Index,
      ((ExecutionState.mapClassical
        ((code m ell width sameWires parameter N generator target cells result).execute environment
          Reference state)
        (fun entry => entry.1.read
          (.product (.product parameter previous) (.storage result.toCStorageRef)))).block
            (.product (.product parameterValue previousValue) (.bits outcome))).matrix
              (basis, leftRef) (basis, rightRef)) =
      (((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
        (CompiledMAU.evolvedState m ell width N
          (generator parameterValue) (target parameterValue)) outcome).toReal : ℂ) *
        (∑ basis : ctx.register.Index,
          ((state.mapClassical (fun entry => entry.1.read (.product parameter previous))).block
            (.product parameterValue previousValue)).matrix
              (basis, leftRef) (basis, rightRef)) := by
  let oldRead := CInputRef.product parameter previous
  let oldValue := CShape.Value.product parameterValue previousValue
  let probability := (((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
    (CompiledMAU.evolvedState m ell width N
      (generator parameterValue) (target parameterValue)) outcome).toReal : ℂ)
  have joint := shortDLP_runtimeRound_joint_outcome_reference (environment := environment)
    m ell width sameWires
    parameter N generator target cells result oldRead distinct cellsSeparate resultSeparate
    state seeded oldValue outcome leftRef rightRef
  have before := (ExecutionState.mapClassical_block_referenceFiberSum state
    (fun entry => entry.1.read oldRead) oldValue leftRef rightRef).trans
    (shortDLP_runtimeSeedBlocks_weighted_reference m ell width sameWires N state seeded
      (fun store => if store.read oldRead = oldValue then 1 else 0) leftRef rightRef)
  refine joint.trans (Eq.trans ?_ (congrArg (fun value : ℂ => probability * value) before.symm))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro original _
  by_cases selected : original.read oldRead = oldValue
  · have parameterRead := congrArg CShape.Value.first selected
    change original.read parameter = parameterValue at parameterRead
    simp only [if_pos selected, one_mul, parameterRead]
    rfl
  · simp only [if_neg selected, zero_mul, mul_zero]

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
