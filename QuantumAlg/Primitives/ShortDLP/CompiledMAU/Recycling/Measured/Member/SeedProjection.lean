/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Preparation.Comparison
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Canonical
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Projection

/-!
# True seeded input and the complete retained caller observation

Only mathematical input histories are grouped. An arbitrary finite observer
of the actual final Store is preserved, provided its invariance under the
actual arithmetic writes has been proved. Every physical/reference matrix
entry and every original Store fiber remain [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev SeedProjectionCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
  (generator target : (ZMod modulus.toNat)ˣ)

/-- The true complete seeded observation equals its internal unit-one/reference comparison. -/
lemma member_seeded_projection_comparison (environment : model.Environment)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (SeedProjectionCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state)
    {Observation : Type} [Fintype Observation]
    (observation : Store (SeedProjectionCtx base noQuantum m ell width) → Observation) :
    ((member base noQuantum m ell width wide modulus generator target).execute environment
        Reference state).mapClassical
          (fun entry => observation entry.1) =
      ((member base noQuantum m ell width wide modulus generator target).execute environment
        Reference (encodeUnitState base noQuantum m ell width modulus
          (unitSeedComparison base noQuantum m ell width modulus state))).mapClassical
            (fun entry => observation entry.1) := by
  rw [unitSeedComparison_encoded base noQuantum m ell width modulus state seeded]
  have natural := Circuit.execute_mapHistory
    (member base noQuantum m ell width wide modulus generator target) environment Reference state
    (fun _ => ())
  have observed := congrArg
    (fun output : State (SeedProjectionCtx base noQuantum m ell width) Reference
        (model.HiddenState × (Unit ×
          (member base noQuantum m ell width wide modulus generator target).Path)) =>
      output.mapClassical
        (fun entry => observation entry.1)) natural
  refine (observed.trans ?_).symm
  exact (ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)
    ((member base noQuantum m ell width wide modulus generator target).execute environment
      Reference state)
    (fun entry => (entry.1, (entry.2.1, ((), entry.2.2.2))))
    (fun entry => observation entry.1)).trans
      (ExecutionState.executionState_mapClassical_congr _ rfl)

/-- The actual seeded output has the canonical same-partner posterior with its full reference. -/
lemma member_seeded_projection_blocks (positive : 0 < modulus.toNat)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (SeedProjectionCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state)
    {Observation : Type} [Fintype Observation]
    (observation : Store (SeedProjectionCtx base noQuantum m ell width) → Observation)
    (agrees : ∀ store arithmetic readout,
      observation (memberActualRecord base noQuantum m ell width modulus wide generator target
        store ((memberOutcomeEquiv base noQuantum m ell width modulus wide generator target).symm
          (arithmetic, readout))).1 =
        observation (memberReadoutStore base noQuantum m ell width store readout))
    (observed : Observation) :
    ((((member base noQuantum m ell width wide modulus generator target).execute environment
      Reference state).mapClassical
        (fun entry => observation entry.1)).block observed).matrix
        =
      let embedding := BasisEmbedding.matrix
        (zeroJointEmbedding base noQuantum m ell width modulus Reference)
      let comparison := unitSeedComparison base noQuantum m ell width modulus state
      ∑ original : Store (SeedProjectionCtx base noQuantum m ell width) ×
          (model.HiddenState × Unit),
        ∑ readout : MemberReadouts m ell,
          let source := canonicalMemberSource m ell width modulus generator target Reference readout
          if observation (memberReadoutStore base noQuantum m ell width original.1 readout) =
              observed then
            embedding * (source * (comparison.block original).matrix * source.conjTranspose) *
              embedding.conjTranspose
          else 0 := by
  have actual := congrArg
    (fun result : ExecutionState Observation
        ((SeedProjectionCtx base noQuantum m ell width).register.prod Reference) =>
      (result.block observed).matrix)
    (member_seeded_projection_comparison base noQuantum m ell width modulus wide generator target
      environment Reference state seeded observation)
  have comparison := member_projection_blocks base noQuantum m ell width modulus wide generator
    target positive environment Reference
    (unitSeedComparison base noQuantum m ell width modulus state) observation agrees observed
  refine actual.trans (comparison.trans ?_)
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro readout _
  rw [memberReadoutSource_canonical m ell width modulus generator target base noQuantum
    Reference original.1 readout]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
