/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.ConditionalOutcome

/-!
# Finite weighted observations of the actual conditional round

An arbitrary complex weight may depend on the actual sampled parameter,
earlier stored data and the new packed result. Its full reference entry after
the real round is the source-probability weighted observation of the same
input store-reference state. This finite linear identity permits induction
through later rounds without assuming independence of earlier outcomes.

Weights and finite sums are mathematical observations of the existing
execution state. The actual quantum member, Z writes, pack, reset and reload
remain the sole executed instructions.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private theorem sum_by_readout {Basis Outcome : Type} [Fintype Basis] [Fintype Outcome]
    (decision : DecidableEq Outcome) (readout : Basis → Outcome)
    (value : Basis → ℂ) (weight : Outcome → ℂ) :
    (∑ basis : Basis, weight (readout basis) * value basis) =
      ∑ outcome : Outcome, weight outcome *
        ∑ basis : Basis, @ite ℂ (readout basis = outcome)
          (decision (readout basis) outcome) (value basis) 0 := by
  symm
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- Joint finite weights follow the source outcome probabilities on the same input state. -/
theorem shortDLP_runtimeRound_weighted_outcome_reference
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
    (state : State ctx Reference History) (seeded : HasSeedBlocks m ell width sameWires N state)
    (weight : (CShape.product parameterShape previousShape).Value →
      (CShape.bits (resultBits m ell width)).Value → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code m ell width sameWires parameter N generator target cells result).execute
        Reference state)
      (fun entry _ => weight (entry.1.read (.product parameter previous))
        (entry.1.read (.storage result.toCStorageRef))) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => ∑ outcome : Fin (resultBits m ell width) → Bool,
          (((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
            (CompiledMAU.evolvedState m ell width N
              (generator (entry.1.read parameter)) (target (entry.1.read parameter)))
                outcome).toReal : ℂ) *
            weight (entry.1.read (.product parameter previous)) (.bits outcome))
        leftRef rightRef := by
  let oldRead := CInputRef.product parameter previous
  let inputWeight := fun store : Store ctx =>
    ∑ outcome : Fin (resultBits m ell width) → Bool,
      (((ShortDLP.measurement (registerParameters m ell width)).outcomePMF
        (CompiledMAU.evolvedState m ell width N
          (generator (store.read parameter)) (target (store.read parameter))) outcome).toReal : ℂ) *
        weight (store.read oldRead) (.bits outcome)
  let packedWeight := fun store : Store ctx => fun basis : ctx.register.Index =>
    weight ((packedBasisStore m ell width sameWires cells result store basis).read oldRead)
      ((packedBasisStore m ell width sameWires cells result store basis).read
        (.storage result.toCStorageRef))
  have measured := shortDLP_runtimeRound_referenceFiberSum m ell width sameWires parameter N
    generator target cells result state
    (fun store => weight (store.read oldRead) (store.read (.storage result.toCStorageRef)))
    leftRef rightRef
  have selected := shortDLP_runtimeSelected_source_fiber m ell width sameWires parameter N
    generator target state seeded packedWeight leftRef rightRef
  have before := shortDLP_runtimeSeedBlocks_weighted_reference m ell width sameWires N
    state seeded inputWeight leftRef rightRef
  refine measured.trans (selected.trans (Eq.trans ?_ before.symm))
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  let source := CompiledMAU.evolvedState m ell width N
    (generator (original.read parameter)) (target (original.read parameter))
  let readout := fun basis : ctx.register.Index =>
    (ShortDLP.measurement (registerParameters m ell width)).readout
      (RuntimePlacement.basisEquiv m ell width sameWires basis)
  let amplitude := fun basis : ctx.register.Index =>
    ‖source.normalized (RuntimePlacement.basisEquiv m ell width sameWires basis)‖ ^ 2
  let coefficient :=
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      ((RuntimePlacement.basisEquiv m ell width sameWires).symm
        (CompiledMAU.reloadLabel m ell width N), leftRef)
      ((RuntimePlacement.basisEquiv m ell width sameWires).symm
        (CompiledMAU.reloadLabel m ell width N), rightRef)
  have packed (basis : ctx.register.Index) : packedWeight original basis =
      weight (original.read oldRead) (.bits (readout basis)) :=
    congrArg₂ weight
      (shortDLP_runtimePacked_read_preserved m ell width sameWires cells result oldRead
        cellsSeparate resultSeparate original basis)
      (shortDLP_runtimePacked_output m ell width sameWires cells result distinct original basis)
  have terms :
      (∑ basis : ctx.register.Index, packedWeight original basis *
        ((amplitude basis : ℂ) * coefficient)) =
      (∑ basis : ctx.register.Index,
        weight (original.read oldRead) (.bits (readout basis)) * (amplitude basis : ℂ)) *
          coefficient := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro basis _
    rw [packed, mul_assoc]
  refine terms.trans (congrArg (fun value : ℂ => value * coefficient) ?_)
  have grouped := sum_by_readout Fintype.decidablePiFintype readout
    (fun basis => (amplitude basis : ℂ))
    (fun outcome => weight (original.read oldRead) (.bits outcome))
  refine grouped.trans ?_
  apply Finset.sum_congr rfl
  intro outcome _
  have fiber := (weighted_fiber (fun basis => readout basis = outcome)
    (fun basis => Fintype.decidablePiFintype (readout basis) outcome) amplitude 1).trans
      (congrArg (fun value : ℝ => (value : ℂ) * 1)
        (RuntimePlacement.shortDLP_runtimeBorn_outcome_weight m ell width sameWires N
          (generator (original.read parameter)) (target (original.read parameter)) outcome))
  have probability :
      (∑ basis : ctx.register.Index,
        if readout basis = outcome then (amplitude basis : ℂ) else 0) =
      (((ShortDLP.measurement (registerParameters m ell width)).outcomePMF source
        outcome).toReal : ℂ) := by
    simpa only [mul_one, ite_mul, one_mul, zero_mul] using fiber
  exact (congrArg (fun value : ℂ => weight (original.read oldRead) (.bits outcome) * value)
    probability).trans (mul_comm _ _)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
