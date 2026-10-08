/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset
import all QuantumAlg.Core.Execution.Measurement.Matrix

/-!
# Actual Z branches select the same native numerator word

The existing sequential measurement interpreter keeps a matrix entry
exactly when its two labels agree on the measured physical wires. For the
actual numerator readouts this is precisely equality of the native Y word.
Their real stored result likewise indexes that same word's literal reset
sequence. Both facts hold for arbitrary other word and history coordinates
[LYL+26, sec_point_add/sec_point_add.tex:67-81].
-/

namespace QuantumAlg.MeasuredUncompute.NumeratorObservation

noncomputable section

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement

/-- The native numerator is the unchanged low word of the actual full frame encoding. -/
def word (width : Nat) (basis : (context width).register.Index) : Fin (2 ^ width) :=
  ((prodEquiv (m := (encoding width).width) (n := width)).symm (frameBasis width basis)).2

theorem word_bit (width : Nat) (basis : (context width).register.Index) (index : Fin width) :
    (frameBasis width basis).val.testBit index.val = (word width basis).val.testBit index.val := by
  have bits := prodEquiv_testBit_right
    ((prodEquiv (m := (encoding width).width) (n := width)).symm (frameBasis width basis)).1
    ((prodEquiv (m := (encoding width).width) (n := width)).symm (frameBasis width basis)).2 index
  have packed : prodEquiv (m := (encoding width).width) (n := width)
      (((prodEquiv (m := (encoding width).width) (n := width)).symm (frameBasis width basis)).1,
        ((prodEquiv (m := (encoding width).width) (n := width)).symm (frameBasis width basis)).2) =
      frameBasis width basis :=
    (prodEquiv (m := (encoding width).width) (n := width)).apply_symm_apply _
  exact (congrArg (fun value => value.val.testBit index.val) packed).symm.trans bits

private theorem agree_iff {ctx : RuntimeCtx .quantum} (readouts : List (ZReadout ctx))
    (left right : ctx.register.Index) :
    Circuit.measurementLabelsAgree readouts left right ↔
      ∀ item ∈ readouts, left item.wire = right item.wire := by
  induction readouts with
  | nil => simp [Circuit.measurementLabelsAgree]
  | cons head tail induction =>
      simp only [Circuit.measurementLabelsAgree, induction, List.mem_cons, forall_eq_or_imp]

private theorem wire_eq_of_bit_eq (width : Nat) (left right : (context width).register.Index)
    (index : Fin width)
    (same : decide ((left (wire width index)).val = 1) =
      decide ((right (wire width index)).val = 1)) :
    left (wire width index) = right (wire width index) := by
  apply Fin.ext
  have dimension : (((context width).quantumLayout.wire (wire width index)).dimension : Nat) = 2 :=
    congrArg PNat.val (wire_dimension width index)
  have leftBound : (left (wire width index)).val < 2 := by
    exact lt_of_lt_of_eq (left (wire width index)).isLt dimension
  have rightBound : (right (wire width index)).val < 2 := by
    exact lt_of_lt_of_eq (right (wire width index)).isLt dimension
  by_cases first : (left (wire width index)).val = 1 <;>
    by_cases second : (right (wire width index)).val = 1 <;> simp_all
  omega

/-- Agreement in the actual interpreter is exactly equality of the physical native Y word. -/
theorem measurement_agrees (width : Nat) (left right : (context width).register.Index) :
    Circuit.measurementLabelsAgree (readouts width) left right ↔
      word width left = word width right := by
  rw [agree_iff]
  constructor
  · intro same
    apply Nat.FixedWidth.word_eq_of_testBit_eq
    intro index
    have equal := same
      (QubitReadouts.readout (wire width index) (wire_dimension width index) (cell width index))
      (List.mem_ofFn.mpr ⟨index, rfl⟩)
    have bits := congrArg (fun value => decide (value.val = 1)) equal
    exact (word_bit width left index).symm.trans ((wire_basis_bit width left index).symm.trans
      (bits.trans ((wire_basis_bit width right index).trans (word_bit width right index))))
  · intro same item present
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp present
    apply wire_eq_of_bit_eq width left right index
    rw [wire_basis_bit, wire_basis_bit, word_bit, word_bit, same]

/-- The actual stored finite results index precisely the native word measured on that branch. -/
theorem stored_outcome (width : Nat) (store : Store (context width))
    (basis : (context width).register.Index) :
    NumeratorReset.outcome ((Circuit.writeMeasurementPath (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts width) store
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model)
        (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
        (readouts width) basis)).read (input width)) =
        word width basis := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro index
  rw [NumeratorReset.outcome_bit, stored_native_mask, word_bit]

end

end QuantumAlg.MeasuredUncompute.NumeratorObservation
