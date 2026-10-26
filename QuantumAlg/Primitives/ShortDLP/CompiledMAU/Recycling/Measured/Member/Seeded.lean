/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Comparison
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Canonical
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Readout.Store

/-!
# Actual seeded member observations preserve the complete reference posterior

History naturality compares the same real member on the actual complete seed
with its internally derived unit-one/reference representation. Both original
output tuples and the entire physical quantum/reference matrix remain
[G25, main.tex:199-295; GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev SeededMemberCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
  (generator target : (ZMod modulus.toNat)ˣ)

/-- The true complete seeded observation equals its internal unit-one/reference comparison. -/
lemma member_seeded_observation_comparison (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (SeededMemberCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state) :
    ((member base noQuantum m ell width wide modulus generator target).execute environment
        Reference state).mapClassical
          (fun entry => (resultRead base noQuantum m ell width).eval entry.1) =
      ((member base noQuantum m ell width wide modulus generator target).execute environment
        Reference (encodeUnitState base noQuantum m ell width modulus
          (unitSeedComparison base noQuantum m ell width modulus state))).mapClassical
            (fun entry => (resultRead base noQuantum m ell width).eval entry.1) := by
  rw [unitSeedComparison_encoded base noQuantum m ell width modulus state seeded]
  have natural := Circuit.execute_mapHistory
    (member base noQuantum m ell width wide modulus generator target) environment Reference state
    (fun _ => ())
  have observed := congrArg
    (fun output : State (SeededMemberCtx base noQuantum m ell width) Reference
        (model.HiddenState × (Unit ×
          (member base noQuantum m ell width wide modulus generator target).Path)) =>
      output.mapClassical
        (fun entry => (resultRead base noQuantum m ell width).eval entry.1)) natural
  refine (observed.trans ?_).symm
  exact (ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)
    ((member base noQuantum m ell width wide modulus generator target).execute environment
      Reference state)
    (fun entry => (entry.1, (entry.2.1, ((), entry.2.2.2))))
    (fun entry => (resultRead base noQuantum m ell width).eval entry.1)).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- The actual seeded output has the canonical same-partner posterior with its full reference. -/
lemma member_seeded_observed_blocks (positive : 0 < modulus.toNat)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (SeededMemberCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state)
    (observed : CShape.Value (.fixedVector (resultBits m ell) (.finite 2))) :
    ((((member base noQuantum m ell width wide modulus generator target).execute environment
      Reference state).mapClassical
        (fun entry => (resultRead base noQuantum m ell width).eval entry.1)).block observed).matrix
        =
      let embedding := BasisEmbedding.matrix
        (zeroJointEmbedding base noQuantum m ell width modulus Reference)
      let comparison := unitSeedComparison base noQuantum m ell width modulus state
      ∑ original : Store (SeededMemberCtx base noQuantum m ell width) × (model.HiddenState × Unit),
        ∑ readout : MemberReadouts m ell,
          let source := canonicalMemberSource m ell width modulus generator target Reference readout
          if memberReadoutValue m ell readout = observed then
            embedding * (source * (comparison.block original).matrix * source.conjTranspose) *
              embedding.conjTranspose
          else 0 := by
  have actual := congrArg
    (fun result : ExecutionState
        (CShape.Value (.fixedVector (resultBits m ell) (.finite 2)))
        ((SeededMemberCtx base noQuantum m ell width).register.prod Reference) =>
      (result.block observed).matrix)
    (member_seeded_observation_comparison base noQuantum m ell width modulus wide generator target
      environment Reference state seeded)
  have comparison := member_observed_blocks base noQuantum m ell width modulus wide generator
    target positive environment Reference
    (unitSeedComparison base noQuantum m ell width modulus state) observed
  refine actual.trans (comparison.trans ?_)
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro readout _
  have resultValue := memberReadoutStore_resultRead base noQuantum m ell width original.1 readout
  have source := memberReadoutSource_canonical m ell width modulus generator target base noQuantum
    Reference original.1 readout
  by_cases selected : memberReadoutValue m ell readout = observed
  · rw [if_pos selected, if_pos (resultValue.trans selected), source]
  · rw [if_neg selected]
    apply if_neg
    intro hit
    exact selected (resultValue.symm.trans hit)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
