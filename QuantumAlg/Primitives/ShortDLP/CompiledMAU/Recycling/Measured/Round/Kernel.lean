/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Round
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Selection
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Parent.Kernel
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Packing.Parent
import all QuantumAlg.Core.Execution.Composition.Identity
import all QuantumAlg.Core.Execution.Reference.Observation

/-!
# Conditional reference kernel of the actual selected measured round

The branch reads its true complete old Store. Its actual member, paid packing
and complete reset/reload have the original source weights while retaining
the entire parent Store and both Reference coordinates. Seed support is an
internal invariant established by actual preparation and restart
[G25, main.tex:199-295,354-360; GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Round

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev RoundKernelCtx := context base noQuantum m ell width

variable {shape : CShape}
  (parameter : CInputRef (RoundKernelCtx base noQuantum m ell width) shape)
  (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
  (generator target : shape.Value → (ZMod modulus.toNat)ˣ)

/-- The stored parameter's actual branch has the original conditional parent/reference kernel. -/
lemma measuredSelected_parent_reference_kernel (positive : 0 < modulus.toNat)
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (RoundKernelCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state)
    (weight : Store base → CShape.Value (.fixedVector (resultBits m ell) (.finite 2)) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((selected base noQuantum m ell width parameter wide modulus generator target).execute
        environment Reference state)
      (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)
        ((resultRead base noQuantum m ell width).eval entry.1)) leftRef rightRef =
      ∑ original : Store (RoundKernelCtx base noQuantum m ell width) × (model.HiddenState × Unit),
        ∑ readout : MemberReadouts m ell,
          let frequency := measuredMemberFrequencies m ell readout
          weight (parentStore base noQuantum m ell width original.1)
              (memberReadoutValue m ell readout) *
            (memberFourierWeight m ell width modulus
              (generator (original.1.read parameter)) (target (original.1.read parameter))
              frequency.1 frequency.2 : ℂ) *
              (state.filterClassical (fun entry => entry.1 = original.1)).referenceMarginal.matrix
                leftRef rightRef := by
  let filtered (value : shape.Value) :=
    state.selectClassical (fun entry => entry.1.read parameter) value
  let body (value : shape.Value) := Circuit.embed
    (allowAllocation := true)
    (ContextEmbedding.identity (RoundKernelCtx base noQuantum m ell width))
    (member base noQuantum m ell width wide modulus (generator value) (target value))
  let coefficient (original : Store (RoundKernelCtx base noQuantum m ell width) ×
      (model.HiddenState × Unit)) (readout : MemberReadouts m ell) (value : shape.Value) :=
    let frequency := measuredMemberFrequencies m ell readout
    weight (parentStore base noQuantum m ell width original.1) (memberReadoutValue m ell readout) *
      (memberFourierWeight m ell width modulus (generator value) (target value)
        frequency.1 frequency.2 : ℂ)
  have branch := measuredSelection_referenceFiberSum (environment := environment)
    parameter body state
    (fun stored _ => weight (parentStore base noQuantum m ell width stored)
      ((resultRead base noQuantum m ell width).eval stored)) leftRef rightRef
  refine branch.trans ?_
  calc
    _ = ∑ value : shape.Value,
        ∑ original : Store (RoundKernelCtx base noQuantum m ell width) ×
          (model.HiddenState × Unit), ∑ readout : MemberReadouts m ell,
          coefficient original readout value *
            (if original.1.read parameter = value then
              (state.filterClassical (fun entry => entry.1 = original.1)).referenceMarginal.matrix
                leftRef rightRef else 0) := by
      apply Finset.sum_congr rfl
      intro value _
      have identity := Circuit.execute_identity_embed
        (allowAllocation := true)
        (member base noQuantum m ell width wide modulus (generator value) (target value))
        environment Reference (filtered value)
      have executed := congrArg
        (fun output => ExecutionState.referenceFiberSum output
          (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)
            ((resultRead base noQuantum m ell width).eval entry.1)) leftRef rightRef) identity
      refine executed.trans ((member_parent_reference_kernel base noQuantum m ell width
        modulus wide (generator value) (target value) positive environment Reference
        (filtered value)
        (measuredSelection_seeded parameter value state _ seeded) weight leftRef rightRef).trans ?_)
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro readout _
      exact congrArg (fun entry : ℂ => coefficient original readout value * entry)
        (measuredSelection_reference_entry parameter value state original.1 leftRef rightRef)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro original _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro readout _
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rfl

/-- The actual paid output write and bank restart propagate the same complete parent kernel. -/
lemma measuredRound_parent_reference_kernel (positive : 0 < modulus.toNat)
    (result : CWriteRef base (.bits (resultBits m ell)))
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (RoundKernelCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state)
    (weight : Store base → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum m ell width parameter wide modulus generator target
        ((parentTransport base noQuantum m ell width).liftWrite result)).execute
          environment Reference state)
      (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)) leftRef rightRef =
      ∑ original : Store (RoundKernelCtx base noQuantum m ell width) × (model.HiddenState × Unit),
        ∑ readout : MemberReadouts m ell,
          let frequency := measuredMemberFrequencies m ell readout
          weight ((parentStore base noQuantum m ell width original.1).write result
              (Packing.packedReadoutValue m ell (memberReadoutValue m ell readout))) *
            (memberFourierWeight m ell width modulus
              (generator (original.1.read parameter)) (target (original.1.read parameter))
              frequency.1 frequency.2 : ℂ) *
              (state.filterClassical (fun entry => entry.1 = original.1)).referenceMarginal.matrix
                leftRef rightRef := by
  have restart := measuredRound_reference_afterPack (environment := environment)
    base noQuantum m ell width parameter wide modulus generator target
    ((parentTransport base noQuantum m ell width).liftWrite result) state
    (fun stored => weight (parentStore base noQuantum m ell width stored)) leftRef rightRef
  have sequence := Circuit.referenceFiberSum_execute_seq
    (selected base noQuantum m ell width parameter wide modulus generator target)
    (Packing.code base noQuantum m ell width
      ((parentTransport base noQuantum m ell width).liftWrite result))
    environment state (fun stored => weight (parentStore base noQuantum m ell width stored))
    leftRef rightRef
  exact restart.trans (sequence.trans
    ((Packing.measuredPacking_parent_referenceFiberSum base noQuantum m ell width result environment
      ((selected base noQuantum m ell width parameter wide modulus generator target).execute
        environment Reference state) weight leftRef rightRef).trans
      (measuredSelected_parent_reference_kernel base noQuantum m ell width parameter modulus wide
        generator target positive environment Reference state seeded
        (fun stored readout =>
          weight (stored.write result (Packing.packedReadoutValue m ell readout)))
        leftRef rightRef)))

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Round
