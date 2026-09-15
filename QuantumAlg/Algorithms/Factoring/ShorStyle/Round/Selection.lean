/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Round
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Seed
import all QuantumAlg.Core.Execution.Selected.Store

/-!
# Stored-value selection of the actual Shor amplitudes

The real sampler parameter chooses the real compiled member in each complete
classical store. On the internally established bank seed, its matrix column
is the member's exact normalized amplitude. The calculation preserves every
entry of that same store's reference block, including off-diagonal entries.

The seed invariant is established by actual preparation and reset/reload.
It is not an additional endpoint input promise or a supplied probability law.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound

noncomputable section

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

private theorem member_seed_column
    (parameter : CShape.Value (ParameterShape (modulusBits N))) (row : ctx.register.Index) :
    (NativePlacement.memberProgram N sameWires parameter).matrix row
        ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) =
      (NativeQuantum.program parameter).applyNormalized
        (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N))
          (NativeQuantum.seedLabel N)) (NativePlacement.basisEquiv N sameWires row) := by
  refine (NativePlacement.member_matrix_entry N sameWires parameter row _).trans ?_
  rw [Equiv.apply_symm_apply]
  exact (HilbertOperator.applyVec_ket
    ((NativeQuantum.program parameter).matrix : HilbertOperator (Qubits
      (NativeQuantum.totalQubits N))) (NativeQuantum.seedLabel N)
    (NativePlacement.basisEquiv N sameWires row)).symm

/-- The actual stored parameter determines both amplitudes of its full reference block. -/
theorem selected_seed_store_entry (parameter : CInputRef ctx (ParameterShape (modulusBits N)))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History)
    (seeded : BasisSeeded.Holds
      ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) state)
    (original : Store ctx) (left right : ctx.register.Index)
    (leftRef rightRef : Reference.Index) :
    (ExecutionState.filterClassical
      ((selected N sameWires parameter).execute Reference state)
      (fun entry => entry.1 = original)).quantumMarginal.matrix
        (left, leftRef) (right, rightRef) =
      (NativeQuantum.program (original.read parameter)).applyNormalized
        (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N))
          (NativeQuantum.seedLabel N)) (NativePlacement.basisEquiv N sameWires left) *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N), leftRef)
          ((NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N), rightRef) *
        star ((NativeQuantum.program (original.read parameter)).applyNormalized
          (NormalizedVector.ket (R := Qubits (NativeQuantum.totalQubits N))
            (NativeQuantum.seedLabel N)) (NativePlacement.basisEquiv N sameWires right)) := by
  let seed := (NativePlacement.basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)
  let coefficient :=
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      (seed, leftRef) (seed, rightRef)
  have actual := congrArg
    (fun matrix : HilbertOperator (Register.prod ctx.register Reference) =>
      matrix (left, leftRef) (right, rightRef))
    (Circuit.selectedUnitary_store_matrix parameter
      (NativePlacement.memberProgram N sameWires)
      (NativePlacement.member_physicalIdx N sameWires) state original)
  refine actual.trans ((BasisSeeded.unitary_entry seed state seeded
    (NativePlacement.memberProgram N sameWires (original.read parameter)).matrix
    original left right leftRef rightRef).trans ?_)
  exact congrArg₂ (fun first second : ℂ => first * coefficient * star second)
    (member_seed_column N sameWires (original.read parameter) left)
    (member_seed_column N sameWires (original.read parameter) right)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativeRound
