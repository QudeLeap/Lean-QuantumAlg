/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Runtime.Round.Semantics

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

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private theorem ket_factor {R : Register} (seed left right : R.Index) (coefficient : ℂ) :
    NormalizedVector.ket (R := R) seed left * coefficient *
        star (NormalizedVector.ket (R := R) seed right) =
      if left = seed ∧ right = seed then coefficient else 0 := by
  by_cases hleft : left = seed <;> by_cases hright : right = seed <;>
    simp [hleft, hright]

variable {ctx : RuntimeCtx .quantum} (m ell width : Nat)
  (sameWires : ctx.quantumWires = (runtimeLayout m ell width).wires)

/-- An internal invariant of the actual complete store-reference blocks on the owned bank. -/
def HasSeedBlocks (N : Nat) {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) : Prop :=
  let seed := (RuntimePlacement.basisEquiv m ell width sameWires).symm
    (CompiledMAU.reloadLabel m ell width N)
  ∀ (original : Store ctx) (left right : ctx.register.Index) (leftRef rightRef : Reference.Index),
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      if left = seed ∧ right = seed then
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef)
      else 0

private theorem seed_blocks_of_entries (N : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (coefficient : Store ctx → Reference.Index → Reference.Index → ℂ)
    (entries : ∀ (original : Store ctx) (left right : ctx.register.Index)
      (leftRef rightRef : Reference.Index),
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (left, leftRef) (right, rightRef) =
        NormalizedVector.ket (R := ctx.register)
            ((RuntimePlacement.basisEquiv m ell width sameWires).symm
              (CompiledMAU.reloadLabel m ell width N)) left *
          coefficient original leftRef rightRef *
          star (NormalizedVector.ket (R := ctx.register)
            ((RuntimePlacement.basisEquiv m ell width sameWires).symm
              (CompiledMAU.reloadLabel m ell width N)) right)) :
    HasSeedBlocks m ell width sameWires N state := by
  let seed := (RuntimePlacement.basisEquiv m ell width sameWires).symm
    (CompiledMAU.reloadLabel m ell width N)
  intro original left right leftRef rightRef
  have atSeed := entries original seed seed leftRef rightRef
  have seedFactor := ket_factor seed seed seed (coefficient original leftRef rightRef)
  have seedValue :
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef) = coefficient original leftRef rightRef :=
    atSeed.trans (seedFactor.trans (if_pos ⟨rfl, rfl⟩))
  exact (entries original left right leftRef rightRef).trans
    ((ket_factor seed left right (coefficient original leftRef rightRef)).trans
      (congrArg (fun value : ℂ => if left = seed ∧ right = seed then value else 0)
        seedValue.symm))

/-- The actual reset/reload establishes the internal seed invariant on every complete store. -/
theorem shortDLP_runtimeResetReload_seedBlocks (N : Nat)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    HasSeedBlocks m ell width sameWires N
      ((resetReload m ell width sameWires N).execute Reference state) :=
  seed_blocks_of_entries m ell width sameWires N _
    (fun original leftRef rightRef => ∑ basis : ctx.register.Index,
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (basis, leftRef) (basis, rightRef))
    (shortDLP_runtimeResetReload_store_entry m ell width sameWires N state)

/-- Each complete actual round reestablishes the seed, regardless of its incoming state. -/
theorem shortDLP_runtimeRound_seedBlocks {shape : CShape}
    (parameter : CInputRef ctx shape) (N : Nat) (generator target : shape.Value → (ZMod N)ˣ)
    (cells : Fin (resultBits m ell width) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (resultBits m ell width)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    HasSeedBlocks m ell width sameWires N
      ((code m ell width sameWires parameter N generator target cells result).execute
        Reference state) :=
  seed_blocks_of_entries m ell width sameWires N _
    (fun original leftRef rightRef => ExecutionState.referenceFiberSum
      ((selected m ell width sameWires parameter N generator target).execute Reference state)
      (fun entry basis =>
        if packedBasisStore m ell width sameWires cells result entry.1 basis = original
        then 1 else 0) leftRef rightRef)
    (shortDLP_runtimeRound_store_reference_entry m ell width sameWires parameter N
      generator target cells result state)

/-- The seed entry is exactly the complete reference block after summing the local bank. -/
theorem shortDLP_runtimeSeedBlocks_reference_entry (N : Nat)
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
          (CompiledMAU.reloadLabel m ell width N), rightRef) := by
  let seed := (RuntimePlacement.basisEquiv m ell width sameWires).symm
    (CompiledMAU.reloadLabel m ell width N)
  have entries :
      (∑ basis : ctx.register.Index,
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (basis, leftRef) (basis, rightRef)) =
      ∑ basis : ctx.register.Index, if basis = seed then
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (seed, leftRef) (seed, rightRef) else 0 := by
    apply Finset.sum_congr rfl
    intro basis _
    simpa only [and_self] using seeded original basis basis leftRef rightRef
  exact entries.trans (by
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl)

end

end QuantumAlg.ShortDLP.CompiledMAU.RuntimeRound
