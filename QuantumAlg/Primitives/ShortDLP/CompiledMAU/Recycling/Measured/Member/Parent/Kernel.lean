/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Parent

/-!
# Actual full-parent conditional kernel of one internally seeded measured member

Every old parent value remains beside its complete Reference coefficient.
The original output tuple has the independently identified source Born
weight. Actual arithmetic records are summed only after their physical
write invariance has been proved [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ParentKernelCtx := context base noQuantum m ell width

/-- All complex observations of the full old parent and real outputs have the true kernel. -/
lemma member_parent_reference_kernel (modulus : BitVec width) [NeZero modulus.toNat]
    (wide : 2 ≤ width) (generator target : (ZMod modulus.toNat)ˣ)
    (positive : 0 < modulus.toNat) (environment : model.Environment) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (ParentKernelCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state)
    (weight : Store base → CShape.Value (.fixedVector (resultBits m ell) (.finite 2)) → ℂ)
    (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((member base noQuantum m ell width wide modulus generator target).execute environment
        Reference state)
      (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)
        ((resultRead base noQuantum m ell width).eval entry.1)) leftRef rightRef =
      ∑ original : Store (ParentKernelCtx base noQuantum m ell width) × (model.HiddenState × Unit),
        ∑ readout : MemberReadouts m ell,
          let frequency := measuredMemberFrequencies m ell readout
          weight (parentStore base noQuantum m ell width original.1)
              (memberReadoutValue m ell readout) *
            (memberFourierWeight m ell width modulus generator target frequency.1 frequency.2 : ℂ) *
              (state.filterClassical (fun entry => entry.1 = original.1)).referenceMarginal.matrix
                leftRef rightRef := by
  have actual := member_projection_reference_kernel base noQuantum m ell width modulus wide
    generator target positive environment Reference state seeded
    (memberParentObservation base noQuantum m ell width)
    (memberParentObservation_agrees base noQuantum m ell width modulus wide generator target)
    (fun observed => weight observed.1 observed.2) leftRef rightRef
  refine actual.trans ?_
  apply Finset.sum_congr rfl
  intro original _
  apply Finset.sum_congr rfl
  intro readout _
  rw [memberParentObservation_readout]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
