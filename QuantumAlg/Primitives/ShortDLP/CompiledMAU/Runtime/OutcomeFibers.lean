/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Observation
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Packed.Frame
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Born.Weights

/-!
# The actual new outcome jointly with earlier data and the complete reference

An actual structural read of earlier data and the newest result has the
source conditional outcome probability in each old complete store block.
The coefficient multiplying that probability is the old block's full
reference entry, not an independently specified state. Thus sampled
parameters, previous outcomes and borrowed classical correlations survive
the observation used for repeated-round probability calculations.

The key-separation hypotheses describe the internal retained layout. The
seed hypothesis is the internal fact established by actual preparation and
reset/reload. Neither is an additional endpoint caller state assumption.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma product_bits_eq {shape : CShape} {count : Nat}
    (left right : shape.Value) (bits outcome : Fin count → Bool) :
    CShape.Value.product left (.bits bits) = CShape.Value.product right (.bits outcome) ↔
      left = right ∧ bits = outcome := by
  simp only [CShape.Value.product.injEq, CShape.Value.bits.injEq]

private lemma weighted_fiber {Basis : Type} [Fintype Basis]
    (predicate : Basis → Prop) (decision : DecidablePred predicate)
    (value : Basis → ℝ) (coefficient : ℂ) :
    (∑ basis : Basis, (@ite ℂ (predicate basis) (decision basis) 1 0) *
      ((value basis : ℂ) * coefficient)) =
      ((∑ basis : Basis,
        @ite ℝ (predicate basis) (decision basis) (value basis) 0 : ℝ) : ℂ) * coefficient := by
  have terms :
      (∑ basis : Basis, (@ite ℂ (predicate basis) (decision basis) 1 0) *
        ((value basis : ℂ) * coefficient)) =
      ∑ basis : Basis,
        ((@ite ℝ (predicate basis) (decision basis) (value basis) 0) : ℂ) * coefficient := by
    apply Finset.sum_congr rfl
    intro basis _
    by_cases selected : predicate basis
    · simp only [if_pos selected, one_mul]
    · simp only [if_neg selected, zero_mul, Complex.ofReal_zero]
  exact terms.trans ((Finset.sum_mul _ _ _).symm.trans
    (congrArg (fun total : ℂ => total * coefficient)
      (Complex.ofReal_sum (s := Finset.univ)
        (fun basis => @ite ℝ (predicate basis) (decision basis) (value basis) 0)).symm))

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- Earlier data and the actual newest outcome retain the source-weighted full reference block. -/
lemma shortDLP_runtimeRound_joint_outcome_reference {parameterShape observedShape : CShape}
    (parameter : CInputRef ctx parameterShape) (N : Nat)
    (generator target : parameterShape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    (observed : CInputRef ctx observedShape)
    (distinct : Function.Injective (fun index => (cells index).key))
    (cellsSeparate : ∀ index, (cells index).key ∉ observed.storageKeys)
    (resultSeparate : result.key ∉ observed.storageKeys)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (seeded : HasSeedBlocks m ell width sameWires N state)
    (oldValue : observedShape.Value) (outcome : Fin (resultBits m ell width) → Bool)
    (leftRef rightRef : Reference.Index) :
    (∑ basis : ctx.register.Index,
      ((ExecutionState.mapClassical
        ((code m ell width sameWires parameter N generator target cells result).execute environment
          Reference state)
        (fun entry => entry.1.read (.product observed (.storage result.toCStorageRef)))).block
          (.product oldValue (.bits outcome))).matrix (basis, leftRef) (basis, rightRef)) =
      ∑ original : Store ctx, if original.read observed = oldValue then
        (((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
          (CompiledMAU.evolvedState m ell width N
            (generator (original.read parameter)) (target (original.read parameter)))
              outcome).toReal : ℂ) *
          (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
            ((RuntimePlacement.basisEquiv m ell width sameWires).symm
              (CompiledMAU.reloadLabel m ell width N), leftRef)
            ((RuntimePlacement.basisEquiv m ell width sameWires).symm
              (CompiledMAU.reloadLabel m ell width N), rightRef)
        else 0 := by
  let observe := fun store : Store ctx =>
    store.read (.product observed (.storage result.toCStorageRef))
  let weight := fun original : Store ctx => fun basis : ctx.register.Index =>
    if observe (packedBasisStore m ell width sameWires cells result original basis) =
      CShape.Value.product oldValue (.bits outcome) then (1 : ℂ) else 0
  have measured := shortDLP_runtimeRound_observed_reference_entry (environment := environment)
    m ell width sameWires
    parameter N generator target cells result state observe
    (CShape.Value.product oldValue (.bits outcome)) leftRef rightRef
  refine measured.trans ((shortDLP_runtimeSelected_source_fiber m ell width sameWires
    parameter N generator target state seeded weight leftRef rightRef).trans ?_)
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  let source := CompiledMAU.evolvedState m ell width N
    (generator (original.read parameter)) (target (original.read parameter))
  let coefficient :=
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      ((RuntimePlacement.basisEquiv m ell width sameWires).symm
        (CompiledMAU.reloadLabel m ell width N), leftRef)
      ((RuntimePlacement.basisEquiv m ell width sameWires).symm
        (CompiledMAU.reloadLabel m ell width N), rightRef)
  let predicate := fun basis : ctx.register.Index =>
    (ShortDLP.measurement (registerParameters m ell width)).readout
      (RuntimePlacement.basisEquiv m ell width sameWires basis) = outcome
  have weights (basis : ctx.register.Index) : weight original basis =
      if original.read observed = oldValue ∧ predicate basis then 1 else 0 := by
    have read := shortDLP_runtimePacked_joint_read m ell width sameWires cells result observed
      distinct cellsSeparate resultSeparate original basis
    have equal := product_bits_eq (original.read observed) oldValue
      ((ShortDLP.measurement (registerParameters m ell width)).readout
        (RuntimePlacement.basisEquiv m ell width sameWires basis)) outcome
    unfold weight observe
    rw [read]
    by_cases selected : original.read observed = oldValue ∧ predicate basis
    · exact (if_pos (equal.mpr selected)).trans (if_pos selected).symm
    · exact (if_neg (fun found => selected (equal.mp found))).trans (if_neg selected).symm
  by_cases earlier : original.read observed = oldValue
  · rw [if_pos earlier]
    have terms :
        (∑ basis : ctx.register.Index, weight original basis *
          (((‖source.normalized
            (RuntimePlacement.basisEquiv m ell width sameWires basis)‖ ^ 2 : ℝ) : ℂ) *
              coefficient)) =
        ∑ basis : ctx.register.Index, (if predicate basis then (1 : ℂ) else 0) *
          (((‖source.normalized
            (RuntimePlacement.basisEquiv m ell width sameWires basis)‖ ^ 2 : ℝ) : ℂ) *
              coefficient) := by
      apply Finset.sum_congr rfl
      intro basis _
      simp only [weights, earlier, true_and]
    refine terms.trans ((weighted_fiber predicate
      (fun basis => Fintype.decidablePiFintype
        ((ShortDLP.measurement (registerParameters m ell width)).readout
          (RuntimePlacement.basisEquiv m ell width sameWires basis)) outcome)
      (fun basis =>
        ‖source.normalized (RuntimePlacement.basisEquiv m ell width sameWires basis)‖ ^ 2)
      coefficient).trans ?_)
    exact congrArg (fun probability : ℝ => (probability : ℂ) * coefficient)
      (RuntimePlacement.shortDLP_runtimeBorn_outcome_weight m ell width sameWires N
        (generator (original.read parameter)) (target (original.read parameter)) outcome)
  · rw [if_neg earlier]
    apply Finset.sum_eq_zero
    intro basis _
    simp only [weights, earlier, false_and, if_false, zero_mul]

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
