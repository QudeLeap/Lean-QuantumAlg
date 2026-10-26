/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Operator
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Record.Readout

/-!
# Actual arithmetic preserves all retained cells used by the paid feedback

The separation condition concerns only allocated physical storage. It is
proved for each original exponent bank, without restricting any original
Store value, measurement outcome or coherent reference [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Addition.Gidney.Measured.Instruction
open MAU.Multiplication.Gidney.Measured

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Two actual Stores agreeing on all output cells select the same complete paid phase product. -/
lemma feedbackScalar_congr (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (position : Fin bits) (first second : Store (Context base noQuantum m ell width))
    (same : ∀ index,
      first.read (.storage (outputs index).toCStorageRef) =
        second.read (.storage (outputs index).toCStorageRef))
    (count : Nat) (bounded : count ≤ position.val) :
    feedbackScalar base noQuantum m ell width inverse outputs position count bounded first =
      feedbackScalar base noQuantum m ell width inverse outputs position count bounded second := by
  induction count with
  | zero => rfl
  | succ count induction =>
      simp only [feedbackScalar, same, induction (by omega)]

variable (modulus : BitVec width) [NeZero modulus.toNat]

omit [NeZero modulus.toNat] in
/-- Reused arithmetic cells cannot change any phase chosen from a separate output bank. -/
lemma stageArithmetic_feedbackScalar (wide : 2 ≤ width) (inverse : Bool) {bits : Nat}
    (outputs : Fin bits → CWriteRef (Context base noQuantum m ell width) (.finite 2))
    (separate : ∀ vent index,
      (ventCell base noQuantum m ell width vent).key ≠ (outputs index).key)
    (unit : (ZMod modulus.toNat)ˣ) (position : Fin bits)
    (store : Store (Context base noQuantum m ell width))
    (measured : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit position) :
    feedbackScalar base noQuantum m ell width inverse outputs position position.val le_rfl
        (stageArithmeticRecord base noQuantum m ell width modulus wide unit position store
          measured).1 =
      feedbackScalar base noQuantum m ell width inverse outputs position position.val le_rfl
        store := by
  apply feedbackScalar_congr
  intro index
  exact wordActualRecord_read_other (Physical.qubits width)
    (context_wires base noQuantum m ell width) (ventCell base noQuantum m ell width)
    (outputs index).toCStorageRef (fun vent => separate vent index) _ store measured

/-- The actual first exponent uses only outputs physically separate from every reused vent cell. -/
lemma firstCell_vent_distinct (vent : Fin (width - 2)) (index : Fin (ell + m)) :
    (ventCell base noQuantum m ell width vent).key ≠
      (firstCell base noQuantum m ell width index).key :=
  vent_result_distinct base noQuantum m ell width vent (Fin.castAdd ell index)

/-- The actual second exponent's output bank is also physically separate from every reused vent. -/
lemma secondCell_vent_distinct (vent : Fin (width - 2)) (index : Fin ell) :
    (ventCell base noQuantum m ell width vent).key ≠
      (secondCell base noQuantum m ell width index).key :=
  vent_result_distinct base noQuantum m ell width vent (Fin.natAdd (ell + m) index)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
