/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Semantics
import all QuantumAlg.Core.Execution.Basis.Seeded

/-!
# The actual reusable seed in every complete store-reference block

The internal invariant below refers only to entries of the actual state.
Each store's reference coefficient is that state's own seed-coordinate
entry, with no separately supplied state or probability witness. Distinct
reference coordinates are retained, and zero-probability stores are allowed.

Actual reset/reload and the complete actual round establish this invariant
without any input promise. It is an internal induction fact for reuse of the
one owned bank, not an initialization requirement imposed on an endpoint's
caller. In particular, all actual parameter and previous-result storage
remains part of the store indexing these blocks.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound

noncomputable section

variable {environment :
  (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- An internal invariant of the actual complete store-reference blocks on the owned bank. -/
abbrev HasSeedBlocks (N : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) : Prop :=
  BasisSeeded.Holds ((RuntimePlacement.basisEquiv m ell width sameWires).symm
    (CompiledMAU.reloadLabel m ell width N)) state

/-- The actual reset/reload establishes the internal seed invariant on every complete store. -/
lemma shortDLP_runtimeResetReload_seedBlocks (N : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    HasSeedBlocks m ell width sameWires N
      ((resetReload m ell width sameWires N).execute environment Reference state) :=
  BasisSeeded.of_entries ((RuntimePlacement.basisEquiv m ell width sameWires).symm
    (CompiledMAU.reloadLabel m ell width N)) _
    (fun original leftRef rightRef => ∑ basis : ctx.register.Index,
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (basis, leftRef) (basis, rightRef))
    (shortDLP_runtimeResetReload_store_entry m ell width sameWires N state)

/-- Each complete actual round reestablishes the seed, regardless of its incoming state. -/
lemma shortDLP_runtimeRound_seedBlocks {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    HasSeedBlocks m ell width sameWires N
      ((code m ell width sameWires parameter N generator target cells result).execute environment
        Reference state) :=
  BasisSeeded.of_entries ((RuntimePlacement.basisEquiv m ell width sameWires).symm
    (CompiledMAU.reloadLabel m ell width N)) _
    (fun original leftRef rightRef => ExecutionState.referenceFiberSum
      ((selected m ell width sameWires parameter N generator target).execute
        environment Reference state)
      (fun entry basis =>
        if packedBasisStore m ell width sameWires cells result entry.1 basis = original
        then 1 else 0) leftRef rightRef)
    (shortDLP_runtimeRound_store_reference_entry m ell width sameWires parameter N
      generator target cells result state)

/-- The seed entry is exactly the complete reference block after summing the local bank. -/
lemma shortDLP_runtimeSeedBlocks_reference_entry (N : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (seeded : HasSeedBlocks m ell width sameWires N state)
    (original : Store ctx) (leftRef rightRef : Reference.Index) :
    (∑ basis : ctx.register.Index,
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (basis, leftRef) (basis, rightRef)) =
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (CompiledMAU.reloadLabel m ell width N), leftRef)
        ((RuntimePlacement.basisEquiv m ell width sameWires).symm
          (CompiledMAU.reloadLabel m ell width N), rightRef) :=
  BasisSeeded.reference_entry _ state seeded original leftRef rightRef

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
