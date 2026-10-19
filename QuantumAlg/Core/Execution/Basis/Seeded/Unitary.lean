/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Unitary.StoreFilter

/-!
# Native basis loading preserves complete store-reference seed blocks

An actual local unitary that takes one basis ket to another transports the
complete stored seed invariant. Every classical store retains its reference
coefficient, including off-diagonal reference entries. The native circuit,
service state and execution path remain those of the unitary instruction.
-/

namespace QuantumAlg.Execution.BasisSeeded

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Exact native loading transports the intrinsic seed of every complete store block. -/
lemma unitary {allowAllocation : Bool} {gates : GateModel} {oracles : OracleModel}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}
    {ctx : RuntimeCtx .quantum} {Reference : Register} {History : Type} [Fintype History]
    (program : UnitaryCircuit gates oracles ctx.quantumLayout)
    (environment : (ExecutionModel.quantum gates oracles operations services).Environment)
    (input output : ctx.register.Index)
    (action : program.applyNormalized environment.quantum (NormalizedVector.ket input) =
      NormalizedVector.ket output)
    (state : State ctx Reference (services.HiddenState × History))
    (seeded : Holds input state) :
    Holds output ((Circuit.unitary (allowAllocation := allowAllocation)
      (operations := operations) (classicalOracles := services)
      program).execute environment Reference state) := by
  have column (row : ctx.register.Index) :
      (program.matrix environment.quantum) row input
        = NormalizedVector.ket (R := ctx.register) output row := by
    have entry := congrArg (fun vector : NormalizedVector ctx.register => vector row) action
    change (program.matrix environment.quantum).applyVec
      (NormalizedVector.ket input).vec row = _ at entry
    rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at entry
    exact entry
  apply of_entries output _ (fun original leftRef rightRef =>
    (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
      (input, leftRef) (input, rightRef))
  intro original left right leftRef rightRef
  have actual := congrArg
    (fun density : DensityOperator (Register.prod ctx.register Reference) =>
      density.matrix (left, leftRef) (right, rightRef))
    (Circuit.unitary_store_filter (allowAllocation := allowAllocation)
      (operations := operations) program environment state
      (fun store => store = original))
  exact actual.trans ((unitary_entry input state seeded (program.matrix environment.quantum)
    original
    left right leftRef rightRef).trans
      (congrArg₂ (fun first second : ℂ => first *
        (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix
          (input, leftRef) (input, rightRef) * star second)
        (column left) (column right)))

end

end QuantumAlg.Execution.BasisSeeded
