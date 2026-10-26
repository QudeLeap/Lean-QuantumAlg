/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Round.Kernel
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Frame.Observation

/-!
# Backward parent-Store kernel for the real measured round

Only the caller's stored parameter chooses the two source units. The actual
member, paid output packing and bank restart propagate every complex parent
observation and its complete Reference coefficient through the same program
[G25, main.tex:199-295,354-360; GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Round

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

/-- The unchanged original source weights transport a weight on the actual packed parent Store. -/
def parentReferenceKernel {shape : CShape} (parameter : CInputRef base shape)
    (modulus : BitVec width) [NeZero modulus.toNat]
    (generator target : shape.Value → (ZMod modulus.toNat)ˣ)
    (result : CWriteRef base (.bits (resultBits m ell)))
    (weight : Store base → ℂ) (stored : Store base) : ℂ :=
  ∑ readout : MemberReadouts m ell,
    let frequency := measuredMemberFrequencies m ell readout
    weight (stored.write result
      (Packing.packedReadoutValue m ell (memberReadoutValue m ell readout))) *
      (memberFourierWeight m ell width modulus (generator (stored.read parameter))
        (target (stored.read parameter)) frequency.1 frequency.2 : ℂ)

/-- Actual conditional execution pulls every parent/reference weight to its true input Store. -/
lemma measuredRound_parent_referenceFiberSum {shape : CShape} (parameter : CInputRef base shape)
    (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
    (generator target : shape.Value → (ZMod modulus.toNat)ˣ) (positive : 0 < modulus.toNat)
    (result : CWriteRef base (.bits (resultBits m ell)))
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (context base noQuantum m ell width) Reference (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state)
    (weight : Store base → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum m ell width
        ((parentTransport base noQuantum m ell width).liftInput parameter) wide modulus
        generator target ((parentTransport base noQuantum m ell width).liftWrite result)).execute
          environment Reference state)
      (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)) leftRef rightRef =
      ExecutionState.referenceFiberSum state
        (fun entry _ => parentReferenceKernel base m ell width parameter modulus generator target
          result weight (parentStore base noQuantum m ell width entry.1)) leftRef rightRef := by
  refine (measuredRound_parent_reference_kernel base noQuantum m ell width
    ((parentTransport base noQuantum m ell width).liftInput parameter) modulus wide generator target
    positive result environment Reference state seeded weight leftRef rightRef).trans ?_
  refine Eq.trans ?_ (measuredParent_referenceFiberSum base noQuantum m ell width state
    (parentReferenceKernel base m ell width parameter modulus generator target result weight)
    leftRef rightRef).symm
  apply Finset.sum_congr rfl
  intro original _
  let reference : ℂ :=
    (state.filterClassical (fun entry => entry.1 = original.1)).referenceMarginal.matrix
      leftRef rightRef
  let coefficient (readout : MemberReadouts m ell) : ℂ :=
    let frequency := measuredMemberFrequencies m ell readout
    weight ((parentStore base noQuantum m ell width original.1).write result
        (Packing.packedReadoutValue m ell (memberReadoutValue m ell readout))) *
      (memberFourierWeight m ell width modulus
        (generator ((parentStore base noQuantum m ell width original.1).read parameter))
        (target ((parentStore base noQuantum m ell width original.1).read parameter))
        frequency.1 frequency.2 : ℂ)
  have distribute : (∑ readout : MemberReadouts m ell, coefficient readout) * reference =
      ∑ readout : MemberReadouts m ell, coefficient readout * reference :=
    Finset.sum_mul _ _ _
  refine Eq.trans ?_ distribute.symm
  apply Finset.sum_congr rfl
  intro readout _
  have actualRead :=
    (parentTransport base noQuantum m ell width).workspaceTransport_restrict_readsAs
      original.1 parameter
  exact congrArg
    (fun value =>
      let frequency := measuredMemberFrequencies m ell readout
      weight ((parentStore base noQuantum m ell width original.1).write result
          (Packing.packedReadoutValue m ell (memberReadoutValue m ell readout))) *
        (memberFourierWeight m ell width modulus (generator value) (target value)
          frequency.1 frequency.2 : ℂ) *
          (state.filterClassical (fun entry => entry.1 = original.1)).referenceMarginal.matrix
            leftRef rightRef) actualRead

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Round
