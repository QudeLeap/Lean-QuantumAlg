/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round.Selection

/-!
# Actual Shor selected-state reference fibers

Each complete stored parameter chooses its compiled amplitude. Summing the
local diagonal retains that store's entire reference entry and weights it
by the corresponding squared amplitude. Earlier results and source samples
remain in the store index throughout this finite sum.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

/-- A weighted actual selected-state fiber retains each source store's complete reference block. -/
theorem selected_reference_fiber (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) state)
    (weight : Store ctx → ctx.register.Index → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum
      ((selected N sameWires parameter).execute Reference state)
      (fun entry basis => weight entry.1 basis) leftRef rightRef =
        ∑ basis : ctx.register.Index, ∑ original : Store ctx, weight original basis *
          (((‖(NativeQuantum.program (original.read parameter)).applyNormalized
            (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N))
              (NativeQuantum.seedLabel N)) (NativePlacement.basisEquiv N sameWires basis)‖ ^ 2 :
                ℝ) : ℂ) *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
              ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N), leftRef)
              ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N),
                rightRef)) := by
  refine (BasisSeeded.fiber_store_blocks
    ((selected N sameWires parameter).execute Reference state) weight leftRef rightRef).trans ?_
  apply Finset.sum_congr rfl
  intro basis _
  apply Finset.sum_congr rfl
  intro original _
  apply congrArg (fun entry : ℂ => weight original basis * entry)
  refine (selected_seed_store_entry N sameWires parameter state seeded original
    basis basis leftRef rightRef).trans ?_
  let amplitude := (NativeQuantum.program (original.read parameter)).applyNormalized
    (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N)) (NativeQuantum.seedLabel N))
      (NativePlacement.basisEquiv N sameWires basis)
  let coefficient :=
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N), leftRef)
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N), rightRef)
  calc
    _ = (amplitude * star amplitude) * coefficient := by ring
    _ = _ := congrArg (fun scalar : ℂ => scalar * coefficient)
      (by simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.mul_conj' amplitude)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
