/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Reference.Preparation
import all QuantumAlg.Core.Execution.State
import all QuantumAlg.Core.Execution.Interpret

/-!
# Exact preparation laws for the single circuit interpreter

The actual preparation instruction tensors its prescribed pure state with
the complete old context-reference operator, then updates the typed store
and path. Summing classical blocks preserves that exact tensor formula
[dW19, qcnotes.tex:5381,8071]. Summing the freshly allocated basis coordinates
recovers every old joint entry, and tracing out the complete local context
therefore preserves every external-reference entry [dW19, qcnotes.tex:6827].

All basis changes below come from the actual appended wire records. The old
context and reference may be mixed and entangled. No preparation callback,
additional interpreter, or operation for discarding physical storage is used.
-/

namespace QuantumAlg.Execution

noncomputable section

variable {systemCount : Nat} {ctx : RuntimeCtx .quantum} {Reference : Register}

/-- Exact local basis assembly from the new and old physical wire records. -/
def preparedLocalBasisEquiv (ctx : RuntimeCtx .quantum) (key : StorageKey)
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (layout.register.Index × ctx.register.Index) ≃
      (ctx.addOwnedLayout key layout fresh disjoint).register.Index :=
  (QuantumLayout.appendBasisEquiv layout ctx.quantumLayout
    (ctx.addOwnedLayout_layoutDisjoint layout disjoint)).symm.trans
      (ctx.addOwnedLayoutBasisEquiv key layout fresh disjoint)

/-- The full preparation correspondence uses the local wire assembly and reference identity. -/
lemma prepareContextBasisEquiv_pair (key : StorageKey)
    (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (newBasis : layout.register.Index) (oldBasis : ctx.register.Index)
    (reference : Reference.Index) :
    prepareContextBasisEquiv ctx Reference key layout fresh disjoint
      (newBasis, (oldBasis, reference)) =
        (preparedLocalBasisEquiv ctx key layout fresh disjoint (newBasis, oldBasis),
          reference) := rfl

variable {C : Type} [Fintype C]

/-- Summing the actual classical blocks retains the full pure-state tensor matrix. -/
lemma prepareContext_quantumMarginal_joined_entry
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (newRow newColumn : layout.register.Index)
    (oldRow oldColumn : (Register.prod ctx.register Reference).Index) :
    (prepareContext state key layout fresh disjoint prepared).quantumMarginal.matrix
      (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newRow, oldRow))
      (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newColumn, oldColumn)) =
        (prepared.vec newRow * star (prepared.vec newColumn)) *
          state.quantumMarginal.matrix oldRow oldColumn := by
  change (∑ value : C,
      ((prepareContext state key layout fresh disjoint prepared).block value).matrix)
        (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newRow, oldRow))
        (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newColumn, oldColumn)) =
    (prepared.vec newRow * star (prepared.vec newColumn)) *
      (∑ value : C, (state.block value).matrix) oldRow oldColumn
  simp only [Matrix.sum_apply, prepareContext_joined_entry, Finset.mul_sum]

/-- Tracing only the new physical systems preserves the entire old context-reference operator. -/
lemma prepareContext_quantumMarginal_old_entry
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register)
    (oldRow oldColumn : (Register.prod ctx.register Reference).Index) :
    (∑ newBasis : layout.register.Index,
      (prepareContext state key layout fresh disjoint prepared).quantumMarginal.matrix
        (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newBasis, oldRow))
        (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newBasis, oldColumn))) =
      state.quantumMarginal.matrix oldRow oldColumn := by
  have normalized :
      (∑ basis : layout.register.Index, prepared.vec basis * star (prepared.vec basis)) = (1 : ℂ) :=
    DensityOperator.trace_pureMatrix (R := layout.register) prepared
  simp only [prepareContext_quantumMarginal_joined_entry]
  rw [← Finset.sum_mul, normalized, one_mul]

/-- Preparation preserves the full reference matrix after tracing all actual local wires. -/
lemma prepareContext_reference_entry
    (state : ExecutionState C (Register.prod ctx.register Reference))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (prepared : NormalizedVector layout.register) (refLeft refRight : Reference.Index) :
    (∑ basis : (ctx.addOwnedLayout key layout fresh disjoint).register.Index,
      (prepareContext state key layout fresh disjoint prepared).quantumMarginal.matrix
        (basis, refLeft) (basis, refRight)) =
      ∑ basis : ctx.register.Index,
        state.quantumMarginal.matrix (basis, refLeft) (basis, refRight) := by
  calc
    _ = ∑ basis : layout.register.Index × ctx.register.Index,
        (prepareContext state key layout fresh disjoint prepared).quantumMarginal.matrix
          (preparedLocalBasisEquiv ctx key layout fresh disjoint basis, refLeft)
          (preparedLocalBasisEquiv ctx key layout fresh disjoint basis, refRight) :=
      ((preparedLocalBasisEquiv ctx key layout fresh disjoint).sum_comp
        (fun basis =>
          (prepareContext state key layout fresh disjoint prepared).quantumMarginal.matrix
            (basis, refLeft) (basis, refRight))).symm
    _ = ∑ oldBasis : ctx.register.Index, ∑ newBasis : layout.register.Index,
        (prepareContext state key layout fresh disjoint prepared).quantumMarginal.matrix
          (prepareContextBasisEquiv ctx Reference key layout fresh disjoint
            (newBasis, (oldBasis, refLeft)))
          (prepareContextBasisEquiv ctx Reference key layout fresh disjoint
            (newBasis, (oldBasis, refRight))) := by
      simp only [Fintype.sum_prod_type, prepareContextBasisEquiv_pair]
      exact Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun oldBasis _ =>
      prepareContext_quantumMarginal_old_entry state key layout fresh disjoint prepared
        (oldBasis, refLeft) (oldBasis, refRight)

namespace State

variable {H : Type} [Fintype H]

/-- The actual typed store extension and path record preserve the prepared quantum marginal. -/
lemma prepare_quantumMarginal (state : State ctx Reference H)
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (preparation : BasisPreparation layout) :
    (state.prepare key layout fresh disjoint preparation).quantumMarginal =
      (prepareContext state key layout fresh disjoint preparation.normalized).quantumMarginal := by
  simp only [prepare, ExecutionState.mapClassical_quantumMarginal]

end State

end

end QuantumAlg.Execution

namespace QuantumAlg.Circuit

open Execution

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
  {operations : ClassicalOpModel} {classicalOracles : ClassicalOracleModel}
  {systemCount : Nat} {ctx : RuntimeCtx .quantum} {Reference : Register}
  {H : Type} [Fintype H]

variable
  (environment : (ExecutionModel.quantum gates oracles operations classicalOracles).Environment)

/-- The single interpreter's zero-preparation case is the actual context-bound state update. -/
lemma execute_prepareZero (state : State ctx Reference (classicalOracles.HiddenState × H))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx) :
    (Circuit.prepareZero (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
      ctx key layout fresh disjoint).execute
      environment Reference state =
      (state.prepare key layout fresh disjoint (BasisPreparation.zero layout)).mapHistory
        (fun record => (record.1.1, (record.1.2, record.2))) := rfl

/-- Every actual preparation output entry contains the complete old joint coherence. -/
lemma prepareZero_joined_entry (state : State ctx Reference (classicalOracles.HiddenState × H))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (newRow newColumn : layout.register.Index)
    (oldRow oldColumn : (Register.prod ctx.register Reference).Index) :
    ((Circuit.prepareZero (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
      ctx key layout fresh disjoint).execute
      environment Reference state).quantumMarginal.matrix
        (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newRow, oldRow))
        (prepareContextBasisEquiv ctx Reference key layout fresh disjoint (newColumn, oldColumn)) =
      ((BasisPreparation.zero layout).normalized.vec newRow *
        star ((BasisPreparation.zero layout).normalized.vec newColumn)) *
        state.quantumMarginal.matrix oldRow oldColumn := by
  rw [execute_prepareZero]
  simp only [State.mapHistory, ExecutionState.mapClassical_quantumMarginal,
    State.prepare_quantumMarginal]
  exact prepareContext_quantumMarginal_joined_entry state key layout fresh disjoint
    (BasisPreparation.zero layout).normalized newRow newColumn oldRow oldColumn

/-- Actual preparation preserves every reference entry, including off-diagonal coherences. -/
lemma prepareZero_reference_entry (state : State ctx Reference (classicalOracles.HiddenState × H))
    (key : StorageKey) (layout : QuantumLayout systemCount) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (refLeft refRight : Reference.Index) :
    (∑ basis : (ctx.addOwnedLayout key layout fresh disjoint).register.Index,
      ((Circuit.prepareZero (gates := gates) (oracles := oracles)
      (operations := operations) (classicalOracles := classicalOracles)
        ctx key layout fresh disjoint).execute
        environment Reference state).quantumMarginal.matrix (basis, refLeft) (basis, refRight)) =
      ∑ basis : ctx.register.Index,
        state.quantumMarginal.matrix (basis, refLeft) (basis, refRight) := by
  rw [execute_prepareZero]
  simp only [State.mapHistory, ExecutionState.mapClassical_quantumMarginal,
    State.prepare_quantumMarginal]
  exact prepareContext_reference_entry state key layout fresh disjoint
    (BasisPreparation.zero layout).normalized refLeft refRight

end

end QuantumAlg.Circuit
