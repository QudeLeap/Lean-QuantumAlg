/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Reset
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Instrument

/-!
# Every actual active-bank Fourier output is physically reset

Each corrected stage preserves every physical coordinate outside its actual
active injection. Structural composition therefore retains already reset
heads while the remaining corrected stages reset their own selected wires.
The complete instrument gives the same zero-row support for arbitrary
original stored mixtures, service histories and external Reference.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- The actual corrected stage is diagonal on every unselected original physical coordinate. -/
lemma window_stageKraus_outside (ports : Ports ctx totalBits (active + 1))
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (outcome : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension)
    (focus : Fin ctx.systemCount) (outside : ∀ index, ports.wires index ≠ focus)
    (row column : (ctx.register.prod Reference).Index)
    (different : row.1 focus ≠ column.1 focus) :
    nativeStageKraus ports environment Reference outcome row column = 0 := by
  have absent : focus ∉ (physicalBankEmbedding ports.wires).selection := by
    intro member
    obtain ⟨index, same⟩ := (physicalBankEmbedding_member ports.wires focus).mp member
    exact outside index same
  let shifted := Function.update row.1 (ports.wires 0)
    (row.1 (ports.wires 0) + outcome)
  have shiftedFocus : shifted focus = row.1 focus :=
    Function.update_of_ne (Ne.symm (outside 0)) _ _
  have complement : (bankCoordinates ports.wires ports.qubits shifted).2 ≠
      (bankCoordinates ports.wires ports.qubits column.1).2 := by
    intro same
    exact different (shiftedFocus.symm.trans
      ((bankCoordinates_complement_eq_iff ports.wires ports.qubits shifted column.1).mp
        same focus absent))
  rw [window_stageKraus_shift_entry]
  change _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.nativeStageKraus
    (environment := environment) true (ports.wires 0) (ports.qubits 0)
      (tailPhysicalWires ports.wires) (fun index => ports.qubits index.succ)
        Reference outcome (shifted, row.2) column = 0
  rw [nativeStageKraus_bank_entry]
  simp only [complement, false_and, and_false, if_false, mul_zero]

private lemma product_preserves_coordinate {Index Value : Type*} [Fintype Index]
    (coordinate : Index → Value) (trailing leading : Matrix Index Index ℂ)
    (trailingSupport : ∀ row column, coordinate row ≠ coordinate column →
      trailing row column = 0)
    (leadingSupport : ∀ row column, coordinate row ≠ coordinate column →
      leading row column = 0)
    (row column : Index) (different : coordinate row ≠ coordinate column) :
    (trailing * leading) row column = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro middle _
  by_cases same : coordinate row = coordinate middle
  · rw [leadingSupport middle column (fun equal => different (same.trans equal)), mul_zero]
  · rw [trailingSupport row middle same, zero_mul]

/-- The complete native branch preserves every original coordinate outside its selected bank. -/
lemma window_outcomeKraus_outside (environment : OracleModel.empty.Interpretation)
    (Reference : Register) (count : Nat) (ports : Ports ctx totalBits count)
    (outcome : Bits count) (focus : Fin ctx.systemCount)
    (outside : ∀ index, ports.wires index ≠ focus)
    (row column : (ctx.register.prod Reference).Index)
    (different : row.1 focus ≠ column.1 focus) :
    outcomeKraus environment Reference count ports outcome row column = 0 := by
  induction count generalizing row column with
  | zero =>
      have unequal : row ≠ column := fun same => different (congrArg (fun basis => basis.1 focus)
        same)
      change (1 : HilbertOperator (ctx.register.prod Reference)) row column = 0
      simp only [Matrix.one_apply, if_neg unequal]
  | succ count ih =>
      rcases outcome with ⟨head, tail⟩
      change (outcomeKraus environment Reference count ports.tail tail *
        nativeStageKraus ports environment Reference (headOutcome ports head)) row column = 0
      exact product_preserves_coordinate (fun basis => basis.1 focus) _ _
        (fun left right unequal => ih ports.tail tail
          (fun index => outside index.succ) left right unequal)
        (fun left right unequal => window_stageKraus_outside ports environment Reference
          (headOutcome ports head) focus outside left right unequal)
        row column different

/-- Every measured native branch has zero rows on every nonzero selected physical bit. -/
lemma window_outcomeKraus_zero_row (environment : OracleModel.empty.Interpretation)
    (Reference : Register) (count : Nat) (ports : Ports ctx totalBits count)
    (outcome : Bits count) (index : Fin count)
    (row column : (ctx.register.prod Reference).Index)
    (nonzero : row.1 (ports.wires index) ≠ 0) :
    outcomeKraus environment Reference count ports outcome row column = 0 := by
  induction count generalizing row column with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      rcases outcome with ⟨head, tail⟩
      change (outcomeKraus environment Reference count ports.tail tail *
        nativeStageKraus ports environment Reference (headOutcome ports head)) row column = 0
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro middle _
      revert nonzero
      refine Fin.cases ?_ (fun next => ?_) index
      · intro nonzero
        by_cases same : row.1 (ports.wires 0) = middle.1 (ports.wires 0)
        · rw [window_stageKraus_zero_row ports environment Reference (headOutcome ports head)
            middle column (fun zero => nonzero (same.trans zero)), mul_zero]
        · rw [window_outcomeKraus_outside environment Reference count ports.tail tail
            (ports.wires 0) (fun next equal => by
              have indices : next.succ = (0 : Fin (count + 1)) := ports.wires.injective equal
              exact Fin.succ_ne_zero next indices) row middle same, zero_mul]
      · intro nonzero
        rw [ih ports.tail tail next row middle nonzero, zero_mul]

/-- All complete stored output densities of the real readout reset the whole active bank. -/
lemma window_readout_store_zero_row
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (count : Nat) (ports : Ports ctx totalBits count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx)
    (index : Fin count) (row column : (ctx.register.prod Reference).Index)
    (nonzero : row.1 (ports.wires index) ≠ 0) :
    (((readout count ports).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix row column = 0 := by
  rw [window_readout_instrument_store_matrix]
  simp only [Matrix.sum_apply, Matrix.ite_apply, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro original _
  apply Finset.sum_eq_zero
  intro outcome _
  by_cases written : outcomeStore count ports original outcome = stored
  · rw [if_pos written]
    exact conjugation_zero_row _ _ row column
      (fun middle => window_outcomeKraus_zero_row environment.quantum Reference count ports
        outcome index row middle nonzero)
  · rw [if_neg written]

/-- Actual same-stream earlier-result feedback followed by readout resets the same entire bank. -/
lemma window_inverseCode_store_zero_row
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (ports : Ports ctx totalBits active)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) (stored : Store ctx)
    (index : Fin active) (row column : (ctx.register.prod Reference).Index)
    (nonzero : row.1 (ports.wires index) ≠ 0) :
    (((inverseCode ports).execute environment Reference state).filterClassical
      (fun entry => entry.1 = stored)).quantumMarginal.matrix row column = 0 := by
  rw [window_inverseCode_store]
  exact window_readout_store_zero_row environment active ports _ stored index row column nonzero

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
