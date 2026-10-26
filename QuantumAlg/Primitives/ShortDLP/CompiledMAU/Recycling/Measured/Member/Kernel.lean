/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Contraction
import all QuantumAlg.Core.Execution.Measurement.Fibers

/-!
# Actual seeded member reference kernel for retained caller observations

The conditional weight comes from the same original source column of the
actual measured program. Every complete old Store and both Reference indices
remain. Only the local quantum bank is traced; observer invariance is a
separate physical-write obligation [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev MemberKernelCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
  (generator target : (ZMod modulus.toNat)ˣ)

/-- Exact reference entries of every retained actual caller observation have the source weight. -/
lemma member_projection_reference_entry (positive : 0 < modulus.toNat)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (MemberKernelCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state)
    {Observation : Type} [Fintype Observation]
    (observation : Store (MemberKernelCtx base noQuantum m ell width) → Observation)
    (agrees : ∀ store arithmetic readout,
      observation (memberActualRecord base noQuantum m ell width modulus wide generator target
        store ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
          (arithmetic, readout))).1 =
        observation (memberReadoutStore base noQuantum m ell width store readout))
    (observed : Observation) (leftRef rightRef : Reference.Index) :
    (∑ basis : (MemberKernelCtx base noQuantum m ell width).register.Index,
      ((((member base noQuantum m ell width wide modulus generator target).execute environment
        Reference state).mapClassical (fun entry => observation entry.1)).block observed).matrix
          (basis, leftRef) (basis, rightRef)) =
      ∑ original : Store (MemberKernelCtx base noQuantum m ell width) ×
          (model.HiddenState × Unit), ∑ readout : MemberReadouts m ell,
        let frequency := measuredMemberFrequencies m ell readout
        if observation (memberReadoutStore base noQuantum m ell width original.1 readout) =
            observed then
          (memberFourierWeight m ell width modulus generator target frequency.1 frequency.2 : ℂ) *
            (state.filterClassical (fun entry => entry.1 = original.1)).referenceMarginal.matrix
              leftRef rightRef
        else 0 := by
  have blocks := member_seeded_projection_blocks base noQuantum m ell width modulus wide generator
    target positive environment Reference state seeded observation agrees observed
  have actual := congrArg
    (fun matrix : HilbertOperator ((MemberKernelCtx base noQuantum m ell width).register.prod
        Reference) =>
      ∑ basis : (MemberKernelCtx base noQuantum m ell width).register.Index,
        matrix (basis, leftRef) (basis, rightRef)) blocks
  refine actual.trans ?_
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro original _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro readout _
  by_cases selected : observation
      (memberReadoutStore base noQuantum m ell width original.1 readout) = observed
  · simp only [selected, if_true]
    exact member_canonical_seed_reference_sum base noQuantum m ell width modulus generator target
      state original readout leftRef rightRef
  · simp only [selected, if_false, Finset.sum_const_zero]

/-- Arbitrary finite caller weights propagate through the actual member's conditional kernel. -/
lemma member_projection_reference_kernel (positive : 0 < modulus.toNat)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (MemberKernelCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state)
    {Observation : Type} [Finite Observation]
    (observation : Store (MemberKernelCtx base noQuantum m ell width) → Observation)
    (agrees : ∀ store arithmetic readout,
      observation (memberActualRecord base noQuantum m ell width modulus wide generator target
        store ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
          (arithmetic, readout))).1 =
        observation (memberReadoutStore base noQuantum m ell width store readout))
    (weight : Observation → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((member base noQuantum m ell width wide modulus generator target).execute environment
        Reference state) (fun entry _ => weight (observation entry.1)) leftRef rightRef =
      ∑ original : Store (MemberKernelCtx base noQuantum m ell width) ×
          (model.HiddenState × Unit), ∑ readout : MemberReadouts m ell,
        let frequency := measuredMemberFrequencies m ell readout
        weight (observation (memberReadoutStore base noQuantum m ell width original.1 readout)) *
          (memberFourierWeight m ell width modulus generator target frequency.1 frequency.2 : ℂ) *
            (state.filterClassical (fun entry => entry.1 = original.1)).referenceMarginal.matrix
              leftRef rightRef := by
  let _ : Fintype Observation := Fintype.ofFinite Observation
  have observed := ExecutionState.referenceFiberSum_mapClassical (decision := inferInstance)
    ((member base noQuantum m ell width wide modulus generator target).execute environment
      Reference state) (fun entry => observation entry.1) (fun value _ => weight value)
    leftRef rightRef
  refine observed.symm.trans ?_
  unfold ExecutionState.referenceFiberSum
  rw [Finset.sum_comm]
  calc
    _ = ∑ value : Observation, weight value *
        (∑ basis : (MemberKernelCtx base noQuantum m ell width).register.Index,
          ((((member base noQuantum m ell width wide modulus generator target).execute environment
            Reference state).mapClassical (fun entry => observation entry.1)).block value).matrix
              (basis, leftRef) (basis, rightRef)) := by
      apply Finset.sum_congr rfl
      intro value _
      exact (Finset.mul_sum _ _ _).symm
    _ = _ := by
      simp_rw [member_projection_reference_entry base noQuantum m ell width modulus wide generator
        target positive environment Reference state seeded observation agrees,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro original _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro readout _
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
