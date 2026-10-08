/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Invariant
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.StoreBlocks
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Born

/-!
# Source amplitudes conditioned on the complete actual stored parameter

On the internally established seed, the actual selected unitary produces
the original compiled source amplitudes in each complete classical store.
Each pair of reference coordinates retains that store's original reference
entry. Thus the later measurement calculation can preserve the actual
sample, parameter, previous outcomes and borrowed classical correlations.

This lemma consumes the internal seed fact established by preparation and
reset/reload. It does not declare a new caller promise or substitute a
probability kernel for the actual selected member execution.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

private theorem source_column (N : Nat) (generator target : (ZMod N)ˣ)
    (row : ctx.register.Index) :
    (RuntimePlacement.memberProgram m ell width sameWires N generator target).matrix row
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (CompiledMAU.reloadLabel m ell width N)) =
      (CompiledMAU.evolvedState m ell width N generator target).normalized
        (RuntimePlacement.basisEquiv m ell width sameWires row) :=
  (HilbertOperator.applyVec_ket
    ((RuntimePlacement.memberProgram m ell width sameWires N generator target).matrix :
      HilbertOperator ctx.register)
    ((RuntimePlacement.basisEquiv m ell width sameWires).symm
      (CompiledMAU.reloadLabel m ell width N)) row).symm.trans
    (RuntimePlacement.shortDLP_runtimeMember_seed_amplitude m ell width sameWires N
      generator target row)

/-- Actual stored parameters determine source amplitudes without losing any reference entry. -/
theorem shortDLP_runtimeSelected_seed_store_entry {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (seeded : HasSeedBlocks m ell width sameWires N state)
    (original : Store ctx) (left right : ctx.register.Index)
    (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical
      ((selected m ell width sameWires parameter N generator target).execute Reference state)
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      (CompiledMAU.evolvedState m ell width N
        (generator (original.read parameter)) (target (original.read parameter))).normalized
          (RuntimePlacement.basisEquiv m ell width sameWires left) *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          ((RuntimePlacement.basisEquiv m ell width sameWires).symm
            (CompiledMAU.reloadLabel m ell width N), leftRef)
          ((RuntimePlacement.basisEquiv m ell width sameWires).symm
            (CompiledMAU.reloadLabel m ell width N), rightRef) *
        star ((CompiledMAU.evolvedState m ell width N
          (generator (original.read parameter)) (target (original.read parameter))).normalized
            (RuntimePlacement.basisEquiv m ell width sameWires right)) := by
  let seed := (RuntimePlacement.basisEquiv m ell width sameWires).symm
    (CompiledMAU.reloadLabel m ell width N)
  let coefficient :=
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      (seed, leftRef) (seed, rightRef)
  have selection := congrArg
    (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
      matrix (left, leftRef) (right, rightRef))
    (shortDLP_runtimeSelected_store_unitary m ell width sameWires parameter N generator target
      state original)
  refine selection.trans ((local_basis_block
    (RuntimePlacement.memberProgram m ell width sameWires N
      (generator (original.read parameter)) (target (original.read parameter))).matrix
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal
    seed left right leftRef rightRef coefficient
    (fun row column => seeded original row column leftRef rightRef)).trans ?_)
  exact congrArg₂ (fun first second : ℂ => first * coefficient * star second)
    (source_column m ell width sameWires N
      (generator (original.read parameter)) (target (original.read parameter)) left)
    (source_column m ell width sameWires N
      (generator (original.read parameter)) (target (original.read parameter)) right)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
