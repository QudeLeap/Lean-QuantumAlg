/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Semantics
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Selection.Fibers

/-!
# The same actual Shor round with its derived source weights

When the real bank has the seed established by preparation or a previous
round, its selected member gives the exact conditional amplitude weights.
The final store therefore contains its actual measurement fiber jointly
with the reloaded seed and the complete old reference operator. The sums
retain all earlier storage rather than separating its classical correlations.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

/-- The complete actual store-reference result has its derived conditional Born weights. -/
theorem round_source_store_entry (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    (cells : Fin (phaseBits N) → CWriteRef ctx (.finite 2))
    (result : CWriteRef ctx (.bits (phaseBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) state)
    (finalStore : Store ctx) (left right : ctx.register.Index)
    (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical
      ((code N sameWires parameter cells result).execute Reference state)
      (fun entry => entry.1 = finalStore)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      NormalizedVector.ket (R := ctx.register)
          ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) left *
        (∑ basis : ctx.register.Index, ∑ original : Store ctx,
          (if packedBasisStore N sameWires cells result original basis = finalStore
            then (1 : ℂ) else 0) *
          (((‖(NativeQuantum.program (original.read parameter)).applyNormalized
            (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N))
              (NativeQuantum.seedLabel N)) (NativePlacement.basisEquiv N sameWires basis)‖ ^ 2 :
                ℝ) : ℂ) *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
              ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N), leftRef)
              ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N),
                rightRef))) *
        star (NormalizedVector.ket (R := ctx.register)
          ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) right) := by
  refine (round_store_reference_entry N sameWires parameter cells result state
    finalStore left right leftRef rightRef).trans ?_
  exact congrArg (fun coefficient : ℂ =>
    NormalizedVector.ket (R := ctx.register)
        ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) left *
      coefficient * star (NormalizedVector.ket (R := ctx.register)
        ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) right))
    (selected_reference_fiber N sameWires parameter state seeded
      (fun original basis =>
        if packedBasisStore N sameWires cells result original basis = finalStore then 1 else 0)
      leftRef rightRef)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
