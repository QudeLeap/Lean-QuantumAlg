/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Seed.Selection
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Classical.Composition

/-!
# Actual conditional reference fibers weighted by the source Born amplitudes

The measurement fiber of the actual selected state is a finite sum over
complete old stores and physical basis labels. Its scalar weight is the
squared norm of the source amplitude chosen by that old store's actual
parameter. Each summand keeps the old store's full reference entry, including
off-diagonal reference coordinates.

The complete-round formula uses the real measured writes and packing output
to select the final store. These finite sums are mathematical observations
of actual execution, not a replacement executor or a prescribed runtime
probability kernel. They retain the sampled parameter and earlier outcomes
as part of every store index.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private theorem source_weight (amplitude coefficient : ℂ) :
    amplitude * coefficient * star amplitude =
      ((‖amplitude‖ ^ 2 : ℝ) : ℂ) * coefficient := by
  calc
    _ = (amplitude * star amplitude) * coefficient := by ring
    _ = _ := congrArg (fun value : ℂ => value * coefficient)
      (by simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.mul_conj' amplitude)

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- Every actual selected-state reference fiber has the conditional source Born weights. -/
theorem shortDLP_runtimeSelected_source_fiber {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (seeded : HasSeedBlocks m ell width sameWires N state)
    (weight : Store ctx → ctx.register.Index → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((selected m ell width sameWires parameter N generator target).execute Reference state)
      (fun entry basis => weight entry.1 basis) leftRef rightRef =
        ∑ basis : ctx.register.Index, ∑ original : Store ctx, weight original basis *
          (((‖(CompiledMAU.evolvedState m ell width N
            (generator (original.read parameter)) (target (original.read parameter))).normalized
              (RuntimePlacement.basisEquiv m ell width sameWires basis)‖ ^ 2 : ℝ) : ℂ) *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
              ((RuntimePlacement.basisEquiv m ell width sameWires).symm
                (CompiledMAU.reloadLabel m ell width N), leftRef)
              ((RuntimePlacement.basisEquiv m ell width sameWires).symm
                (CompiledMAU.reloadLabel m ell width N), rightRef)) := by
  refine (BasisSeeded.fiber_store_blocks
    ((selected m ell width sameWires parameter N generator target).execute Reference state)
    weight leftRef rightRef).trans ?_
  apply Finset.sum_congr rfl
  intro basis _
  apply Finset.sum_congr rfl
  intro original _
  apply congrArg (fun value : ℂ => weight original basis * value)
  exact (shortDLP_runtimeSelected_seed_store_entry m ell width sameWires parameter N
    generator target state seeded original basis basis leftRef rightRef).trans (source_weight _ _)

/-- The final actual store has its source-weighted input reference fiber and the exact seed. -/
theorem shortDLP_runtimeRound_source_store_entry {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History))
    (seeded : HasSeedBlocks m ell width sameWires N state)
    (finalStore : Store ctx) (left right : ctx.register.Index)
    (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical
      ((code m ell width sameWires parameter N generator target cells result).execute
        Reference state)
      (fun entry => entry.1 = finalStore)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      NormalizedVector.ket (R := ctx.register)
          ((RuntimePlacement.basisEquiv m ell width sameWires).symm
            (CompiledMAU.reloadLabel m ell width N)) left *
        (∑ basis : ctx.register.Index, ∑ original : Store ctx,
          (if packedBasisStore m ell width sameWires cells result original basis = finalStore
            then (1 : ℂ) else 0) *
          (((‖(CompiledMAU.evolvedState m ell width N
            (generator (original.read parameter)) (target (original.read parameter))).normalized
              (RuntimePlacement.basisEquiv m ell width sameWires basis)‖ ^ 2 : ℝ) : ℂ) *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
              ((RuntimePlacement.basisEquiv m ell width sameWires).symm
                (CompiledMAU.reloadLabel m ell width N), leftRef)
              ((RuntimePlacement.basisEquiv m ell width sameWires).symm
                (CompiledMAU.reloadLabel m ell width N), rightRef))) *
        star (NormalizedVector.ket (R := ctx.register)
          ((RuntimePlacement.basisEquiv m ell width sameWires).symm
            (CompiledMAU.reloadLabel m ell width N)) right) := by
  refine (shortDLP_runtimeRound_store_reference_entry m ell width sameWires parameter N
    generator target cells result state finalStore left right leftRef rightRef).trans ?_
  exact congrArg (fun coefficient : ℂ =>
    NormalizedVector.ket (R := ctx.register)
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (CompiledMAU.reloadLabel m ell width N)) left * coefficient *
      star (NormalizedVector.ket (R := ctx.register)
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (CompiledMAU.reloadLabel m ell width N)) right))
    (shortDLP_runtimeSelected_source_fiber m ell width sameWires parameter N generator target
      state seeded (fun original basis =>
        if packedBasisStore m ell width sameWires cells result original basis = finalStore
        then 1 else 0) leftRef rightRef)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
