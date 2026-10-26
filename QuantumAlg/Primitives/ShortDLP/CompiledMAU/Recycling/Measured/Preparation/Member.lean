/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Seeded
import all QuantumAlg.Core.Execution.Composition.Identity

/-!
# The actual initialized member supplies its own complete seed comparison

The same run allocates its real frame, allocates its actual retained cells,
loads the unit representative by native X gates, and executes the complete
measured member. No input seed, isometry or instrument certificate is supplied
by the caller [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat) (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
  (generator target : (ZMod modulus.toNat)ˣ)

private abbrev PreparedMemberCtx := context base noQuantum m ell width

omit [NeZero modulus.toNat] in
/-- The true initialized run observes precisely its actual prepared-state member continuation. -/
lemma measuredRun_output_state (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History)) :
    (((run base noQuantum m ell width wide modulus generator target).code.execute environment
      Reference state).mapClassical
        (fun entry => (resultRead base noQuantum m ell width).eval entry.1)) =
      ((member base noQuantum m ell width wide modulus generator target).execute environment
        Reference ((prepare base noQuantum m ell width modulus.toNat).execute environment
          Reference state)).mapClassical
            (fun entry => (resultRead base noQuantum m ell width).eval entry.1) := by
  let first := prepare base noQuantum m ell width modulus.toNat
  let child := member base noQuantum m ell width wide modulus generator target
  let second : Circuit model (PreparedMemberCtx base noQuantum m ell width)
      (PreparedMemberCtx base noQuantum m ell width) :=
    .embed (ContextEmbedding.identity (PreparedMemberCtx base noQuantum m ell width)) child
  have executed := congrArg
    (fun result : State (PreparedMemberCtx base noQuantum m ell width) Reference
        (model.HiddenState × (History × (first.Path × second.Path))) =>
      result.mapClassical (fun entry => (resultRead base noQuantum m ell width).eval entry.1))
    (Circuit.execute_seq (environment := environment) first second state)
  have grouped :
      ((second.execute environment Reference (first.execute environment Reference state)).mapHistory
        (fun history => (history.1, (history.2.1.1, (history.2.1.2, history.2.2))))).mapClassical
          (fun entry => (resultRead base noQuantum m ell width).eval entry.1) =
        (second.execute environment Reference
          (first.execute environment Reference state)).mapClassical
          (fun entry => (resultRead base noQuantum m ell width).eval entry.1) := by
    exact (ExecutionState.executionState_mapClassical_comp_instances (result := inferInstance)
      (second.execute environment Reference (first.execute environment Reference state))
      (fun entry => (entry.1,
        (entry.2.1, (entry.2.2.1.1, (entry.2.2.1.2, entry.2.2.2)))))
      (fun entry => (resultRead base noQuantum m ell width).eval entry.1)).trans
        (ExecutionState.executionState_mapClassical_congr _ rfl)
  have original := Circuit.execute_identity_embed (allowAllocation := true) child environment
    Reference (first.execute environment Reference state)
  exact executed.trans (grouped.trans (congrArg
    (fun result => result.mapClassical
      (fun entry => (resultRead base noQuantum m ell width).eval entry.1)) original))

/-- Real initialization internally supplies the complete unit-one/reference source comparison. -/
lemma measuredRun_seed_comparison (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State base Reference (model.HiddenState × History)) :
    (((run base noQuantum m ell width wide modulus generator target).code.execute environment
      Reference state).mapClassical
        (fun entry => (resultRead base noQuantum m ell width).eval entry.1)) =
      ((member base noQuantum m ell width wide modulus generator target).execute environment
        Reference (encodeUnitState base noQuantum m ell width modulus
          (unitSeedComparison base noQuantum m ell width modulus
            ((prepare base noQuantum m ell width modulus.toNat).execute environment Reference
              state)))).mapClassical
            (fun entry => (resultRead base noQuantum m ell width).eval entry.1) :=
  (measuredRun_output_state base noQuantum m ell width modulus wide generator target environment
    Reference state).trans
      (member_seeded_observation_comparison base noQuantum m ell width modulus wide generator target
        environment Reference
        ((prepare base noQuantum m ell width modulus.toNat).execute environment Reference state)
        (measuredPrepare_seeded base noQuantum m ell width environment modulus.toNat state))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
