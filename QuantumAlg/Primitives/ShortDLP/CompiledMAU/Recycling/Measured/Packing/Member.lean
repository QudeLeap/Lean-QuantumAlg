/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Member.Parent.Kernel
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Packing.Parent

/-!
# The actual measured member and paid packing have one complete parent kernel

The real packing instruction receives the complete actual member posterior.
It writes one existing parent destination and retains all other parent
values and both Reference coordinates. The coefficient is the same original
source weight [G25, main.tex:199-295; GN96, 9511007.tex:214-266].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Packing

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev PackedMemberCtx := context base noQuantum m ell width

/-- Literal paid packing transports the actual full-parent Born kernel to its real destination. -/
lemma measuredPackedMember_parent_reference_kernel
    (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width)
    (generator target : (ZMod modulus.toNat)ˣ) (positive : 0 < modulus.toNat)
    (result : CWriteRef base (.bits (resultBits m ell)))
    (environment : model.Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State (PackedMemberCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (seeded : BasisSeeded.Holds (preparedSeed base noQuantum m ell width modulus.toNat) state)
    (weight : Store base → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((code base noQuantum m ell width
        ((parentTransport base noQuantum m ell width).liftWrite result)).execute environment
          Reference ((member base noQuantum m ell width wide modulus generator target).execute
            environment Reference state))
      (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)) leftRef rightRef =
      ∑ original : Store (PackedMemberCtx base noQuantum m ell width) × (model.HiddenState × Unit),
        ∑ readout : MemberReadouts m ell,
          let frequency := measuredMemberFrequencies m ell readout
          weight ((parentStore base noQuantum m ell width original.1).write result
              (packedReadoutValue m ell (memberReadoutValue m ell readout))) *
            (memberFourierWeight m ell width modulus generator target frequency.1 frequency.2 : ℂ) *
              (state.filterClassical (fun entry => entry.1 = original.1)).referenceMarginal.matrix
                leftRef rightRef :=
  (measuredPacking_parent_referenceFiberSum base noQuantum m ell width result environment
    ((member base noQuantum m ell width wide modulus generator target).execute environment
      Reference state) weight leftRef rightRef).trans
    (member_parent_reference_kernel base noQuantum m ell width modulus wide generator target
      positive environment Reference state seeded
      (fun stored readout => weight (stored.write result (packedReadoutValue m ell readout)))
      leftRef rightRef)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Packing
