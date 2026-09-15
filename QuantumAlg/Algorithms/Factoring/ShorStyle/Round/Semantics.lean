/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Packed
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Reset
import all QuantumAlg.Core.Execution.Store.Blocks

/-!
# The complete actual Shor round and its reusable seed

Stored-value selection, actual Z writes, packing and real reset/reload
compose on the same bank. Each complete final store has the source seed and
the reference operator of its actual selected-state measurement fiber.
This identity holds for an arbitrary incoming state, without normalization,
purity or independence assumptions. The separate amplitude facts identify
its fibers with source probabilities when preparation established the seed.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

/-- Each complete actual round restores the bank seed and retains every measured reference fiber. -/
theorem round_store_reference_entry (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (original : Store ctx)
    (left right : ctx.register.Index) (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical
      ((code N sameWires parameter cells result).execute Reference state)
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      NormalizedVector.ket (R := ctx.register)
          ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) left *
        ExecutionState.referenceFiberSum
          ((selected N sameWires parameter).execute Reference state)
          (fun entry basis =>
            if packedBasisStore N sameWires cells result entry.1 basis = original
            then 1 else 0) leftRef rightRef *
        star (NormalizedVector.ket (R := ctx.register)
          ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) right) := by
  let member := selected N sameWires parameter
  let measurement := Circuit.measurementSequence (readouts N sameWires cells)
  let pack := Circuit.classical (packing N cells result)
  let finish := resetReload N sameWires
  let evolved := member.execute Reference state
  let measured := measurement.execute Reference evolved
  let packed := pack.execute Reference measured
  have first := Circuit.seq_store_marginal member (.seq measurement (.seq pack finish))
    state original
  have second := Circuit.seq_store_marginal measurement (.seq pack finish) evolved original
  have third := Circuit.seq_store_marginal pack finish measured original
  refine (congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      density.matrix (left, leftRef) (right, rightRef))
    (first.trans (second.trans third))).trans ?_
  refine (resetReload_store_entry N sameWires packed original left right leftRef rightRef).trans ?_
  apply congrArg (fun coefficient : ℂ =>
    NormalizedVector.ket (R := ctx.register)
        ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) left *
      coefficient * star (NormalizedVector.ket (R := ctx.register)
        ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) right))
  have grouped := congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      ∑ basis : ctx.register.Index, density.matrix (basis, leftRef) (basis, rightRef))
    (Circuit.seq_store_marginal measurement pack evolved original)
  have observed := congrArg
    (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
      ∑ basis : ctx.register.Index, matrix (basis, leftRef) (basis, rightRef))
    (BasisSeeded.store_matrix ((Circuit.seq measurement pack).execute Reference evolved) original)
  exact grouped.symm.trans (observed.symm.trans
    (packed_reference_entry N sameWires cells result evolved id original leftRef rightRef))

/-- Real reset/reload establishes the seed in every complete actual store block. -/
theorem resetReload_seeded {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N))
      ((resetReload N sameWires).execute Reference state) :=
  BasisSeeded.of_entries _ _
    (fun original leftRef rightRef => ∑ basis : ctx.register.Index,
      (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
        (basis, leftRef) (basis, rightRef))
    (resetReload_store_entry N sameWires state)

/-- Every complete round is ready for another actual member on the same bank. -/
theorem round_seeded (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) :
    BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N))
      ((code N sameWires parameter cells result).execute Reference state) :=
  BasisSeeded.of_entries _ _
    (fun original leftRef rightRef => ExecutionState.referenceFiberSum
      ((selected N sameWires parameter).execute Reference state)
      (fun entry basis =>
        if packedBasisStore N sameWires cells result entry.1 basis = original then 1 else 0)
      leftRef rightRef)
    (round_store_reference_entry N sameWires parameter cells result state)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
