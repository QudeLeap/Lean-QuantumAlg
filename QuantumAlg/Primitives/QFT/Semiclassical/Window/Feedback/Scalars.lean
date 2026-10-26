/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Rows.Feedback
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics

/-!
# Actual stored feedback as the independent partner's phase family

The phase family below is extracted from the same original stored cells and
native rotation factors as the executed feedback word. Its construction is
semantic only: it does not choose runtime syntax or relabel any outcome cell.
The source row and every complementary physical coordinate remain unchanged.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback

noncomputable section

open Execution
open scoped BigOperators

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}

/-- The same stored result selects the same native rotation, independently of the input bit. -/
def onePhase (ports : Ports ctx totalBits active) (previous : BitPosition totalBits)
    (current : Fin active) (stored : Store ctx) : Complex :=
  if ports.past previous then
    if (stored.read (.storage (ports.results previous).toCStorageRef)).toFin.val = 1 then
      Partner.rotation true ((ports.position current).val - previous.2.val - 1)
    else 1
  else 1

/-- The literal chronological product of the earlier-result phases on one selected bit. -/
def atPhase (ports : Ports ctx totalBits active) (current : Fin active) (stored : Store ctx) :
    List (BitPosition totalBits) → Complex
  | [] => 1
  | previous :: rest => atPhase ports current stored rest * onePhase ports previous current stored

/-- All earlier same-stream cell reads, with the exact original physical position offsets. -/
def priorPhases (ports : Ports ctx totalBits active) (stored : Store ctx) : Fin active → Complex :=
  fun current => atPhase ports current stored (previousPositions totalBits)

private lemma oneScalar_factor (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active)
    (stored : Store ctx) (basis : ctx.register.Index) :
    oneScalar ports previous current stored basis =
      if (basis (ports.wires current)).val = 0 then 1
      else onePhase ports previous current stored := by
  by_cases past : ports.past previous <;>
    by_cases selected :
      (stored.read (.storage (ports.results previous).toCStorageRef)).toFin.val = 1 <;>
    by_cases zero : (basis (ports.wires current)).val = 0 <;>
    simp only [oneScalar, phaseScalar, onePhase, past, selected, zero, ↓reduceIte]

private lemma atScalar_factor (ports : Ports ctx totalBits active) (current : Fin active)
    (stored : Store ctx) (basis : ctx.register.Index)
    (previous : List (BitPosition totalBits)) :
    atScalar ports current stored basis previous =
      if (basis (ports.wires current)).val = 0 then 1
      else atPhase ports current stored previous := by
  induction previous with
  | nil => simp only [atScalar, atPhase, ite_self]
  | cons previous rest ih =>
      rw [atScalar, ih, oneScalar_factor]
      by_cases zero : (basis (ports.wires current)).val = 0
      · simp only [if_pos zero, mul_one]
      · simp only [atPhase, if_neg zero]

private lemma wordScalar_list_product (ports : Ports ctx totalBits active) (stored : Store ctx)
    (basis : ctx.register.Index) (current : List (Fin active)) :
    wordScalar ports stored basis current =
      (current.map (fun index =>
        if (basis (ports.wires index)).val = 0 then 1
        else priorPhases ports stored index)).prod := by
  induction current with
  | nil => rfl
  | cons current rest ih =>
      rw [wordScalar, ih, atScalar_factor, List.map_cons, List.prod_cons]
      exact mul_comm _ _

/-- The native feedback scalar equals the independently defined partner phase on the same bits. -/
lemma window_feedback_scalar_phaseBasis (ports : Ports ctx totalBits active) (stored : Store ctx)
    (basis : ctx.register.Index) :
    wordScalar ports stored basis (List.finRange active) =
      Partner.phaseBasis active (priorPhases ports stored)
        (bankCoordinates ports.wires ports.qubits basis).1 := by
  rw [wordScalar_list_product, ← Fin.prod_univ_def]
  unfold Partner.phaseBasis
  apply Finset.prod_congr rfl
  intro index _
  have coordinates := congrFun (bankCoordinates_values ports.wires ports.qubits basis) index
  have zero : tupleCoordinates active (bankCoordinates ports.wires ports.qubits basis).1 index =
      0 ↔ (basis (ports.wires index)).val = 0 := by
    rw [coordinates]
    exact Fin.ext_iff
  by_cases selected : (basis (ports.wires index)).val = 0
  · simp only [if_pos selected, if_pos (zero.mpr selected)]
  · simp only [if_neg selected, if_neg (fun equality => selected (zero.mp equality))]

/-- The actual signed source recurrence is the same negative partner Fourier row. -/
lemma window_signedSource_partner (count : Nat) :
    signedSourceMatrix true count = Partner.fourierRows true count := by
  rw [signedSourceMatrix_inverse OracleModel.empty count OracleModel.emptyInterpretation,
    Partner.qftPartner_fourierRows_negative]

/-- Each actual source coefficient contains the exact prior-cell phase family, with full support. -/
lemma window_source_partner_entry (ports : Ports ctx totalBits active) (Reference : Register)
    (stored : Store ctx) (outcome : Bits active)
    (row column : (ctx.register.prod Reference).Index) :
    sourceWindowKraus ports Reference stored outcome row column =
      if (referenceBankCoordinates ports.wires ports.qubits Reference row).1 =
            Partner.zeroBits active ∧
          (referenceBankCoordinates ports.wires ports.qubits Reference row).2 =
            (referenceBankCoordinates ports.wires ports.qubits Reference column).2 then
        Partner.fourierRows true active outcome
            (referenceBankCoordinates ports.wires ports.qubits Reference column).1 *
          Partner.phaseBasis active (priorPhases ports stored)
            (bankCoordinates ports.wires ports.qubits column.1).1
      else 0 := by
  unfold sourceWindowKraus
  rw [window_signedSource_partner, window_feedback_scalar_phaseBasis]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback
