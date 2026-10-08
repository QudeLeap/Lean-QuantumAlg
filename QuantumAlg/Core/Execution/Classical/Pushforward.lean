/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.ExecutionState
import all QuantumAlg.Core.Algorithm.ExecutionState

/-!
# Complete classical pushforward laws independent of circuit syntax

All original blocks contributing to an output value are summed in full. These
laws depend only on mathematical state maps and preserve reference coherences.
Equality-decision implementations do not change the resulting state.
-/

namespace QuantumAlg.ExecutionState

noncomputable section

private theorem mapClassical_block_matrix_proof {C D : Type} [Fintype C] [Fintype D]
    [DecidableEq D] {R : Register} (state : ExecutionState C R) (update : C → D)
    (result : D) :
    ((state.mapClassical update).block result).matrix =
      ∑ entry : C, if update entry = result then (state.block entry).matrix else 0 := rfl

/-- Every output matrix is the sum of exactly its complete input fiber. -/
public theorem mapClassical_block_matrix {C D : Type} [Fintype C] [Fintype D]
    [DecidableEq D] {R : Register} (state : ExecutionState C R) (update : C → D)
    (result : D) :
    ((state.mapClassical update).block result).matrix =
      ∑ entry : C, if update entry = result then (state.block entry).matrix else 0 :=
  mapClassical_block_matrix_proof state update result

/-- Equal record functions yield equal states for any equality-decision implementations. -/
public theorem executionState_mapClassical_congr {C D : Type} [Fintype C] [Fintype D]
    {R : Register} {first second : DecidableEq D} (state : ExecutionState C R)
    {f g : C → D} (agree : f = g) :
    @mapClassical C D _ _ R first state f = @mapClassical C D _ _ R second state g := by
  cases Subsingleton.elim first second
  cases agree
  rfl

/-- Composition is independent of the equality decisions used at either output boundary. -/
public theorem executionState_mapClassical_comp_instances
    {C D E : Type} [Fintype C] [Fintype D] [Fintype E]
    {R : Register} {middle : DecidableEq D} {last result : DecidableEq E}
    (state : ExecutionState C R) (first : C → D) (second : D → E) :
    @mapClassical D E _ _ R last (@mapClassical C D _ _ R middle state first) second =
      @mapClassical C E _ _ R result state (second ∘ first) :=
  (@executionState_mapClassical_comp C D _ _ R E _ middle last state first second).trans
    (executionState_mapClassical_congr state rfl)

end

end QuantumAlg.ExecutionState
