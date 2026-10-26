/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback.History
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.History

/-!
# Real retained prefix records give the exact inherited suffix phase

The mathematical prefix is decoded from the original stored result cells.
Its coordinate law is proved directly, with no independent outcome witness.
The actual feedback word therefore equals the existing partner recurrence's
inherited phase family, at arbitrary start and active count. No quantum bank
or runtime classical pack is constructed by this mathematical specification.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback

noncomputable section

open Execution
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}

private lemma start_bound (ports : Ports ctx totalBits active) : ports.start ≤ totalBits :=
  (Nat.le_add_right ports.start active).trans ports.within

private def previousIndex (ports : Ports ctx totalBits active) (previous : Fin ports.start) :
    Fin totalBits :=
  ⟨previous.val, previous.isLt.trans_le (start_bound ports)⟩

/-- The exact already-retained same-stream cell values, used only as a mathematical label. -/
def storedPrefix (ports : Ports ctx totalBits active) (stored : Store ctx) : Bits ports.start :=
  (binaryEquiv ports.start).symm (BinaryBasis.bigEndianEquiv ports.start
    (fun previous => (stored.read (.storage
      (ports.results (ports.stream, previousIndex ports previous)).toCStorageRef)).toFin))

lemma window_storedPrefix_coordinate (ports : Ports ctx totalBits active) (stored : Store ctx)
    (previous : Fin ports.start) :
    tupleCoordinates ports.start (storedPrefix ports stored) previous =
      (stored.read (.storage
        (ports.results (ports.stream, previousIndex ports previous)).toCStorageRef)).toFin := by
  simp only [tupleCoordinates, storedPrefix, Equiv.apply_symm_apply]
  exact congrFun ((BinaryBasis.bigEndianEquiv ports.start).symm_apply_apply _) previous

private lemma product_prefix (total start : Nat) (bounded : start ≤ total)
    (factor : Fin total → Complex) (inactive : ∀ index, start ≤ index.val → factor index = 1) :
    (∏ index : Fin total, factor index) =
      ∏ index : Fin start, factor ⟨index.val, index.isLt.trans_le bounded⟩ := by
  let remaining := total - start
  have sameWidth : start + remaining = total := Nat.add_sub_of_le bounded
  refine (Equiv.prod_comp (finCongr sameWidth) factor).symm.trans ?_
  rw [Fin.prod_univ_add]
  have high : (∏ index : Fin remaining,
      factor ((finCongr sameWidth) (index.natAdd start))) = 1 := by
    apply Finset.prod_eq_one
    intro index _
    apply inactive
    change start ≤ start + index.val
    exact Nat.le_add_right _ _
  rw [high, mul_one]
  apply Finset.prod_congr rfl
  intro index _
  exact congrArg factor (Fin.ext rfl)

/-- The actual native history word uses precisely the global prefix factors of its real Store. -/
lemma window_priorPhases_prefix (ports : Ports ctx totalBits active) (stored : Store ctx)
    (current : Fin active) :
    priorPhases ports stored current =
      Partner.historyPhase true ports.start (storedPrefix ports stored) current.val := by
  rw [window_priorPhases_history]
  refine (product_prefix totalBits ports.start (start_bound ports)
    (fun previous =>
      if previous.val < ports.start ∧
          (stored.read (.storage
            (ports.results (ports.stream, previous)).toCStorageRef)).toFin.val = 1 then
        Partner.rotation true ((ports.position current).val - previous.val - 1)
      else 1) (fun previous later => by
        simp only [Nat.not_lt_of_ge later, false_and, ↓reduceIte])).trans ?_
  unfold Partner.historyPhase
  apply Finset.prod_congr rfl
  intro previous _
  have earlier : previous.val < ports.start := previous.isLt
  have coordinates := congrArg Fin.val (window_storedPrefix_coordinate ports stored previous)
  change (tupleCoordinates ports.start (storedPrefix ports stored) previous).val =
    (stored.read (.storage (ports.results (ports.stream,
      ⟨previous.val, previous.isLt.trans_le (start_bound ports)⟩)).toCStorageRef)).toFin.val
      at coordinates
  simp only [earlier, true_and]
  rw [← coordinates]
  by_cases selected : tupleCoordinates ports.start (storedPrefix ports stored) previous = 1
  · have value : (tupleCoordinates ports.start (storedPrefix ports stored) previous).val = 1 :=
      congrArg Fin.val selected
    simp only [if_pos value, if_pos selected]
    rfl
  · have value : (tupleCoordinates ports.start (storedPrefix ports stored) previous).val ≠ 1 :=
      fun equality => selected (Fin.ext equality)
    simp only [if_neg value, if_neg selected]

/-- The same actual retained cells instantiate the old structural suffix-phase recurrence. -/
lemma window_priorPhases_suffix (ports : Ports ctx totalBits active) (stored : Store ctx)
    (current : Fin active) :
    Partner.suffixPhases true ports.start active (fun _ => 1)
        (storedPrefix ports stored) current = priorPhases ports stored current := by
  rw [Partner.qftPartner_suffixPhases_history, window_priorPhases_prefix]
  exact one_mul _

/-- The complete real source row carries exactly the inherited phase of its stored prefix. -/
lemma window_source_suffix_entry (ports : Ports ctx totalBits active) (Reference : Register)
    (stored : Store ctx) (outcome : Bits active)
    (row column : (ctx.register.prod Reference).Index) :
    sourceWindowKraus ports Reference stored outcome row column =
      if (referenceBankCoordinates ports.wires ports.qubits Reference row).1 =
            Partner.zeroBits active ∧
          (referenceBankCoordinates ports.wires ports.qubits Reference row).2 =
            (referenceBankCoordinates ports.wires ports.qubits Reference column).2 then
        Partner.fourierRows true active outcome
            (referenceBankCoordinates ports.wires ports.qubits Reference column).1 *
          Partner.phaseBasis active
            (Partner.suffixPhases true ports.start active (fun _ => 1)
              (storedPrefix ports stored))
            (bankCoordinates ports.wires ports.qubits column.1).1
      else 0 := by
  have actual : priorPhases ports stored =
      Partner.suffixPhases true ports.start active (fun _ => 1) (storedPrefix ports stored) :=
    funext (fun current => (window_priorPhases_suffix ports stored current).symm)
  rw [window_source_partner_entry, actual]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback
