/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Frame
import all QuantumAlg.Core.Execution.Basis.Seeded
import all QuantumAlg.Core.Execution.Reference.Preservation

/-!
# Complete parent-Store observations of the actual measured frame

The local quantum trace keeps both Reference coordinates and every complete
original Store contribution. The fixed empty service model has one hidden
state; no arithmetic output or stored value is deleted
[G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open scoped BigOperators

local instance {A : Type} : DecidableEq A := Classical.decEq A

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ParentObservationCtx := context base noQuantum m ell width

/-- A complete parent weight is exactly the sum of its actual old-Store reference fibers. -/
lemma measuredParent_referenceFiberSum {Reference : Register} {History : Type} [Fintype History]
    (state : State (ParentObservationCtx base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (weight : Store base → ℂ) (leftRef rightRef : Reference.Index) :
    ExecutionState.referenceFiberSum state
      (fun entry _ => weight (parentStore base noQuantum m ell width entry.1)) leftRef rightRef =
      ∑ original : Store (ParentObservationCtx base noQuantum m ell width) ×
          (model.HiddenState × Unit),
        weight (parentStore base noQuantum m ell width original.1) *
          (state.filterClassical (fun entry => entry.1 = original.1)).referenceMarginal.matrix
            leftRef rightRef := by
  refine (BasisSeeded.fiber_store_blocks state
    (fun stored _ => weight (parentStore base noQuantum m ell width stored))
    leftRef rightRef).trans ?_
  rw [Finset.sum_comm, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro original _
  rw [← Finset.mul_sum]
  have reference := ExecutionState.referenceMarginal_entry
    (state.filterClassical (fun entry => entry.1 = original)) leftRef rightRef
  refine (congrArg
    (fun value : ℂ => weight (parentStore base noQuantum m ell width original) * value)
    reference.symm).trans ?_
  let _ : Unique (model.HiddenState × Unit) :=
    { default := ((), ())
      uniq := fun value => by
        rcases value with ⟨left, right⟩
        cases left
        cases right
        rfl }
  exact (Fintype.sum_unique (fun _hidden : model.HiddenState × Unit =>
    weight (parentStore base noQuantum m ell width original) *
      (state.filterClassical (fun entry => entry.1 = original)).referenceMarginal.matrix
        leftRef rightRef)).symm

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
