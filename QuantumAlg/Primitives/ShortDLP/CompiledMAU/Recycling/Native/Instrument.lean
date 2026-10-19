/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Stored.Stage
import all QuantumAlg.Primitives.QFT.Semiclassical.Mathematics
import all QuantumAlg.Core.Execution.Store.History

/-!
# Actual recursive stored instrument of the recycled arithmetic control

Branch matrices are actual native stage
products selected from the real Store after earlier writes. No commutation
or clean-input restriction is needed for this arbitrary-input instrument.
Original Store/hidden/history correlations and arbitrary mixed reference are
retained in the full stored quantum matrix. The operator family is derived
from actual Circuit execution; no certificate is required from a caller.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.NativeInstrument

noncomputable section

open Execution

variable {environment : model.Environment}
open QuantumFourierTransform.Semiclassical (Bits)
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

private lemma storedConjugation_compose_selected {S First Second : Type}
    [Fintype S] [Fintype First] [Fintype Second] {R : Register}
    (before : First → S → S) (after : Second → S → S)
    (leading : S → First → HilbertOperator R) (trailing : S → Second → HilbertOperator R)
    (density : S → HilbertOperator R) (stored : S) :
    (∑ intermediate : S, ∑ second : Second,
      if after second intermediate = stored then
        trailing intermediate second *
          (∑ original : S, ∑ first : First,
            if before first original = intermediate then
              leading original first * density original * (leading original first).conjTranspose
            else 0) * (trailing intermediate second).conjTranspose
      else 0) =
      ∑ original : S, ∑ first : First, ∑ second : Second,
        if after second (before first original) = stored then
          (trailing (before first original) second * leading original first) *
            density original *
            (trailing (before first original) second *
              leading original first).conjTranspose
        else 0 := by
  let contribution (intermediate : S) (second : Second) (original : S) (first : First) :=
    if after second intermediate = stored then
      if before first original = intermediate then
        trailing intermediate second *
          (leading original first * density original * (leading original first).conjTranspose) *
          (trailing intermediate second).conjTranspose
      else 0
    else 0
  calc
    _ = ∑ intermediate : S, ∑ second : Second, ∑ original : S, ∑ first : First,
        contribution intermediate second original first := by
      apply Finset.sum_congr rfl
      intro intermediate _
      apply Finset.sum_congr rfl
      intro second _
      by_cases reaches : after second intermediate = stored
      · simp only [contribution, if_pos reaches, Matrix.mul_sum, Matrix.sum_mul,
          mul_ite, ite_mul, Matrix.mul_zero, Matrix.zero_mul]
      · simp only [contribution, if_neg reaches, Finset.sum_const_zero]
    _ = ∑ original : S, ∑ first : First, ∑ intermediate : S, ∑ second : Second,
        contribution intermediate second original first := by
      have swapped :
          (∑ left : S × Second, ∑ right : S × First,
            contribution left.1 left.2 right.1 right.2) =
          ∑ right : S × First, ∑ left : S × Second,
            contribution left.1 left.2 right.1 right.2 := Finset.sum_comm
      simpa only [Fintype.sum_prod_type] using swapped
    _ = ∑ original : S, ∑ first : First, ∑ second : Second, ∑ intermediate : S,
        contribution intermediate second original first := by
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro first _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro original _
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      rw [Finset.sum_eq_single (before first original)]
      · simp only [contribution, if_true, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      · intro other _ different
        simp only [contribution, if_neg (Ne.symm different), ite_self]
      · intro absent
        exact False.elim (absent (Finset.mem_univ _))

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Every real outcome is written before the next branch reads its actual Store. -/
def suffixStore (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2)) :
    (remaining position : Nat) → position + remaining ≤ bits →
      Store (Context base noQuantum m ell width) → Bits remaining →
        Store (Context base noQuantum m ell width)
  | 0, _, _, original, _ => original
  | remaining + 1, position, bounded, original, (outcome, tail) =>
      suffixStore inverse outputs remaining (position + 1) (by omega)
        (original.write (outputs ⟨position, by omega⟩) (.finite outcome)) tail

/-- Chronological actual branch product; feedback is selected from actual preceding writes. -/
def suffixKraus (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (Reference : Register) :
    (remaining position : Nat) → position + remaining ≤ bits →
      Store (Context base noQuantum m ell width) → Bits remaining →
        HilbertOperator ((Context base noQuantum m ell width).register.prod Reference)
  | 0, _, _, _, _ => 1
  | remaining + 1, position, bounded, original, (outcome, tail) =>
      suffixKraus inverse outputs N unit Reference remaining
        (position + 1) (by omega)
        (original.write (outputs ⟨position, by omega⟩) (.finite outcome)) tail *
          stageKraus (environment := environment) base noQuantum m ell width inverse outputs N unit
            ⟨position, by omega⟩
            Reference original (ContextCoordinates.physicalBit base noQuantum m ell width outcome)

/-- Empty actual execution preserves every complete stored quantum-reference block. -/
private lemma suffix_zero_store (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (position : Nat) (bounded : position + 0 ≤ bits)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (stored : Store (Context base noQuantum m ell width)) :
    ((exponentSuffix base noQuantum m ell width inverse outputs N unit 0 position bounded).execute
      environment
      Reference state |>.filterClassical (fun entry => entry.1 = stored)).quantumMarginal =
      (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal := by
  rw [exponentSuffix, Circuit.execute_id]
  calc
    _ = ((state.mapHistory (fun record => (record.1, (record.2, ())))).filterClassical
        (fun entry => entry.1 = stored)).quantumMarginal := by
      exact congrArg
        (fun result : State (Context base noQuantum m ell width) Reference
            (model.HiddenState × (History × Unit)) =>
          (result.filterClassical (fun entry => entry.1 = stored)).quantumMarginal)
        (State.mapHistory_store_decision
          (ctx := Context base noQuantum m ell width) (Reference := Reference)
          (H := model.HiddenState × History) (K := model.HiddenState × (History × Unit))
          _ state (fun record => (record.1, (record.2, ()))))
    _ = _ := State.mapHistory_store_marginal _ _ _

/-- The actual entire suffix derives its complete adaptive stored instrument. -/
lemma exponentSuffix_store_matrix (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (N : Nat) (unit : (ZMod N)ˣ) (remaining position : Nat)
    (bounded : position + remaining ≤ bits)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context base noQuantum m ell width) Reference
      (model.HiddenState × History))
    (stored : Store (Context base noQuantum m ell width)) :
    (ExecutionState.filterClassical
      ((exponentSuffix base noQuantum m ell width inverse outputs N unit remaining position
        bounded).execute environment Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      ∑ original : Store (Context base noQuantum m ell width), ∑ outcome : Bits remaining,
        if suffixStore base noQuantum m ell width inverse outputs remaining position bounded
            original outcome = stored then
          let operator := suffixKraus (environment := environment) base noQuantum m ell width
            inverse outputs N unit Reference
            remaining position bounded original outcome
          operator *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              operator.conjTranspose
        else 0 := by
  induction remaining generalizing position History with
  | zero =>
      rw [suffix_zero_store]
      let : Unique (Bits 0) := inferInstanceAs (Unique Unit)
      simp only [Fintype.sum_unique, suffixStore, suffixKraus,
        Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  | succ remaining induction =>
      rw [exponentSuffix]
      refine (congrArg DensityOperator.matrix (Circuit.seq_store_marginal
        (stage base noQuantum m ell width inverse outputs N unit ⟨position, by omega⟩)
        (exponentSuffix base noQuantum m ell width inverse outputs N unit remaining
          (position + 1) (by omega)) environment state stored)).trans ?_
      rw [induction]
      simp_rw [StoredStage.stage_store_matrix]
      rw [storedConjugation_compose_selected]
      simp only [Bits, suffixStore, suffixKraus]
      apply Finset.sum_congr rfl
      intro original _
      let contribution (outcome : Fin 2 × Bits remaining) :
          HilbertOperator ((Context base noQuantum m ell width).register.prod Reference) :=
        if suffixStore base noQuantum m ell width inverse outputs (remaining + 1) position
            bounded original outcome = stored then
          let operator := suffixKraus (environment := environment) base noQuantum m ell width
            inverse outputs N unit Reference
            (remaining + 1) position bounded original outcome
          operator *
            (state.filterClassical (fun entry => entry.1 = original)).quantumMarginal.matrix *
              operator.conjTranspose
        else 0
      change (∑ first : Fin 2, ∑ second : Bits remaining, contribution (first, second)) =
        ∑ outcome : Fin 2 × Bits remaining, contribution outcome
      exact (Fintype.sum_prod_type contribution).symm

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.NativeInstrument
