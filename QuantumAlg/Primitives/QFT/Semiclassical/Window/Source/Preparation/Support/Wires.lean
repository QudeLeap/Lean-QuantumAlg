/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Preparation.Support
import all QuantumAlg.Components.QuditShift.Reset.Circuit.Recorded

/-!
# The same zero-wire support in full selected-bank coordinates

The original physical positions and qubit casts determine the recursive bank
tuple. Proved zero support on every actually reset wire therefore gives zero
support of that tuple, with arbitrary complete records and reference data.
No new initial-state condition or physical relabeling is introduced.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source

noncomputable section

private instance wireDimensionNeZero (dimension : ℕ+) : NeZero (dimension : Nat) :=
  ⟨Nat.ne_of_gt dimension.property⟩

variable {ctx : RuntimeCtx .quantum} {count : Nat}

private lemma zero_tuple_coordinate (index : Fin count) :
    tupleCoordinates count (Partner.zeroBits count) index = 0 := by
  rw [tupleCoordinates, window_source_binary_zero]
  change finTwoEquiv.symm ((0 : Nat).testBit index.rev.val) = 0
  rw [Nat.zero_testBit]
  rfl

/-- The tuple is zero exactly when its same original selected physical systems are zero. -/
lemma window_source_bank_zero_iff (wires : Fin count ↪ Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (basis : ctx.register.Index) :
    (bankCoordinates wires qubits basis).1 = Partner.zeroBits count ↔
      ∀ index, basis (wires index) = 0 := by
  constructor
  · intro zero index
    have value := congrFun (bankCoordinates_values wires qubits basis) index
    rw [zero] at value
    have castZero := value.symm.trans (zero_tuple_coordinate index)
    apply Fin.ext
    exact congrArg (fun value : Fin 2 => value.val) castZero
  · intro zero
    apply tupleCoordinates_injective count
    funext index
    rw [congrFun (bankCoordinates_values wires qubits basis) index, zero_tuple_coordinate]
    apply Fin.ext
    exact congrArg
      (fun value : Fin (ctx.quantumLayout.wire (wires index)).dimension => value.val) (zero index)

/-- Complete reset-wire support gives zero-bank diagonal support in every original record. -/
lemma window_source_bank_zero_support {Reference : Register} {Record : Type} [Fintype Record]
    (wires : Fin count ↪ Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (state : ExecutionState Record (ctx.register.prod Reference))
    (supported : ∀ index record (left right : ctx.register.Index)
      (refLeft refRight : Reference.Index), left (wires index) ≠ 0 →
      (state.block record).matrix (left, refLeft) (right, refRight) = 0)
    (record : Record) (basis : (ctx.register.prod Reference).Index)
    (absent : (bankCoordinates wires qubits basis.1).1 ≠ Partner.zeroBits count) :
    (state.block record).matrix basis basis = 0 := by
  classical
  have some : ∃ index, basis.1 (wires index) ≠ 0 := by
    by_contra none
    apply absent
    exact (window_source_bank_zero_iff wires qubits basis.1).mpr
      (fun index => by
        by_contra nonzero
        exact none ⟨index, nonzero⟩)
  obtain ⟨index, nonzero⟩ := some
  exact supported index record basis.1 basis.1 basis.2 basis.2 nonzero

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Source
