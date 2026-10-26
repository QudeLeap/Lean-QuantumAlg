/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Bank
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.SourceRows
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics

/-!
# Source row of the actual measured and reset Fourier head

The native negative-outcome correction changes the output head sector to
zero. Its source amplitude still uses the actual measured bit in both the
Hadamard row and the actual signed tail phase. Full complementary physical
coordinates and Reference remain literal delta factors.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}

private lemma scalar_conditional_congr {First Second : Prop}
    (first : Decidable First) (second : Decidable Second) (same : First ↔ Second)
    {left right : Complex} (actual : left = right) :
    @ite Complex First first left 0 = @ite Complex Second second right 0 := by
  cases first with
  | isTrue yes =>
      cases second with
      | isTrue _ => exact actual
      | isFalse no => exact False.elim (no (same.mp yes))
  | isFalse no =>
      cases second with
      | isTrue yes => exact False.elim (no (same.mpr yes))
      | isFalse _ => rfl

/-- Overwriting the original physical head changes only its selected tuple coordinate. -/
lemma referenceBankCoordinates_overwrite_head (ports : Ports ctx totalBits (active + 1))
    (Reference : Register) (bit : Fin 2) (row : (ctx.register.prod Reference).Index) :
    referenceBankCoordinates ports.wires ports.qubits Reference
        (Function.update row.1 (ports.wires 0) (headOutcome ports bit), row.2) =
      ((bit, (referenceBankCoordinates ports.wires ports.qubits Reference row).1.2),
        (referenceBankCoordinates ports.wires ports.qubits Reference row).2) := by
  let shifted := Function.update row.1 (ports.wires 0) (headOutcome ports bit)
  have outside : ∀ position : Fin ctx.systemCount,
      position ≠ ports.wires 0 → shifted position = row.1 position := by
    intro position different
    exact Function.update_of_ne different _ _
  have rest := (bankCoordinates_outside_head_iff ports.wires ports.qubits shifted row.1).mp outside
  have head : (bankCoordinates ports.wires ports.qubits shifted).1.1 = bit := by
    rw [bankCoordinates_head_value]
    change Fin.cast _ (shifted (ports.wires 0)) = bit
    dsimp only [shifted]
    rw [Function.update_self]
    exact Fin.ext rfl
  change ((bankCoordinates ports.wires ports.qubits shifted).1,
      ((bankCoordinates ports.wires ports.qubits shifted).2, row.2)) =
    ((bit, (bankCoordinates ports.wires ports.qubits row.1).1.2),
      ((bankCoordinates ports.wires ports.qubits row.1).2, row.2))
  exact Prod.ext (Prod.ext head rest.1) (Prod.ext rest.2 rfl)

/-- The real corrected head has the independently defined signed Fourier source amplitude. -/
lemma window_stageKraus_source_entry (ports : Ports ctx totalBits (active + 1))
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (bit : Fin 2) (row column : (ctx.register.prod Reference).Index) :
    let coordinates : (ctx.register.prod Reference).Index ≃
      (Fin 2 × Bits active) ×
        (ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection ×
          Reference.Index) := referenceBankCoordinates ports.wires ports.qubits Reference
    nativeStageKraus ports environment Reference (headOutcome ports bit) row column =
      if (coordinates row).1.1 = 0 ∧
          (coordinates row).1.2 = (coordinates column).1.2 ∧
          (coordinates row).2 = (coordinates column).2 then
        sourcePhaseWeight true active bit (coordinates row).1.2 *
          Gate.HOp bit (coordinates column).1.1 else 0 := by
  dsimp only
  let coordinates : (ctx.register.prod Reference).Index ≃
      (Fin 2 × Bits active) ×
        (ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection ×
          Reference.Index) := referenceBankCoordinates ports.wires ports.qubits Reference
  change nativeStageKraus ports environment Reference (headOutcome ports bit) row column =
    if (coordinates row).1.1 = 0 ∧ (coordinates row).1.2 = (coordinates column).1.2 ∧
        (coordinates row).2 = (coordinates column).2 then
      sourcePhaseWeight true active bit (coordinates row).1.2 *
        Gate.HOp bit (coordinates column).1.1 else 0
  have actualZero : outcomeBit (ports.wires 0) (ports.qubits 0)
      (0 : Fin (ctx.quantumLayout.wire (ports.wires 0)).dimension) = 0 := Fin.ext rfl
  have zeroIff : (coordinates row).1.1 = 0 ↔ row.1 (ports.wires 0) = 0 := by
    change (bankCoordinates ports.wires ports.qubits row.1).1.1 = 0 ↔ _
    simpa only [actualZero] using
      (bankCoordinates_head_outcome_iff ports.wires ports.qubits row.1 0)
  by_cases physicalZero : row.1 (ports.wires 0) = 0
  · rw [window_stageKraus_shift_entry]
    simp only [physicalZero, zero_add]
    change _root_.QuantumAlg.QuantumFourierTransform.Semiclassical.nativeStageKraus
      (environment := environment) true (ports.wires 0) (ports.qubits 0)
        (tailPhysicalWires ports.wires) (fun index => ports.qubits index.succ) Reference
          (headOutcome ports bit)
          (Function.update row.1 (ports.wires 0) (headOutcome ports bit), row.2) column = _
    refine (nativeStageKraus_coordinate_entry (environment := environment) true ports.wires
      ports.qubits Reference bit _ column).trans ?_
    rw [referenceBankCoordinates_overwrite_head]
    change (if bit = bit ∧ (coordinates row).1.2 = (coordinates column).1.2 ∧
        (coordinates row).2 = (coordinates column).2 then
      sourcePhaseWeight true active bit (coordinates row).1.2 *
        Gate.HOp bit (coordinates column).1.1 else 0) = _
    have coordinateZero := zeroIff.mpr physicalZero
    simp only [coordinateZero, true_and]
  · rw [window_stageKraus_zero_row ports environment Reference (headOutcome ports bit)
      row column physicalZero]
    have coordinateNonzero : (coordinates row).1.1 ≠ 0 :=
      fun same => physicalZero (zeroIff.mp same)
    simp only [coordinateNonzero, false_and, if_false]

/-- Complete real corrected branches are the source Fourier rows with a physical zero bank. -/
lemma window_outcomeKraus_source_entry (environment : OracleModel.empty.Interpretation)
    (Reference : Register) :
    ∀ (count : Nat) (ports : Ports ctx totalBits count) (outcome : Bits count)
      (row column : (ctx.register.prod Reference).Index),
      outcomeKraus environment Reference count ports outcome row column =
        if (referenceBankCoordinates ports.wires ports.qubits Reference row).1 =
              Partner.zeroBits count ∧
            (referenceBankCoordinates ports.wires ports.qubits Reference row).2 =
              (referenceBankCoordinates ports.wires ports.qubits Reference column).2 then
          signedSourceMatrix true count outcome
            (referenceBankCoordinates ports.wires ports.qubits Reference column).1 else 0 := by
  intro count
  induction count with
  | zero =>
      intro ports outcome row column
      let coordinates := referenceBankCoordinates ports.wires ports.qubits Reference
      have equality : row = column ↔ (coordinates row).2 = (coordinates column).2 := by
        constructor
        · intro same
          rw [same]
        · intro same
          exact coordinates.injective (Prod.ext (@Subsingleton.elim Unit inferInstance _ _) same)
      have unique : (coordinates row).1 = Partner.zeroBits 0 :=
        @Subsingleton.elim Unit inferInstance _ _
      change (1 : HilbertOperator (ctx.register.prod Reference)) row column =
        if (coordinates row).1 = Partner.zeroBits 0 ∧
            (coordinates row).2 = (coordinates column).2 then 1 else 0
      simp only [Matrix.one_apply, unique, true_and, equality]
  | succ count ih =>
      intro ports outcome row column
      rcases outcome with ⟨head, tail⟩
      let coordinates : (ctx.register.prod Reference).Index ≃
          (Fin 2 × Bits count) ×
            (ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection ×
              Reference.Index) := referenceBankCoordinates ports.wires ports.qubits Reference
      have trailing (middle : (ctx.register.prod Reference).Index) :
          outcomeKraus environment Reference count ports.tail tail row middle =
          if (coordinates row).1.2 = Partner.zeroBits count ∧
              (coordinates row).1.1 = (coordinates middle).1.1 ∧
              (coordinates row).2 = (coordinates middle).2 then
            signedSourceMatrix true count tail (coordinates middle).1.2 else 0 := by
        have selected (basis : (ctx.register.prod Reference).Index) :
            (referenceBankCoordinates ports.tail.wires ports.tail.qubits Reference basis).1 =
              (coordinates basis).1.2 :=
          tailBankCoordinates_selected ports.wires ports.qubits basis.1
        have selectedCondition :
            (referenceBankCoordinates ports.tail.wires ports.tail.qubits Reference row).1 =
              Partner.zeroBits count ↔ (coordinates row).1.2 = Partner.zeroBits count :=
          Iff.of_eq (congrArg (fun input : Bits count => input = Partner.zeroBits count)
            (selected row))
        have remainder :
            (referenceBankCoordinates ports.tail.wires ports.tail.qubits Reference row).2 =
              (referenceBankCoordinates ports.tail.wires ports.tail.qubits Reference middle).2 ↔
              (coordinates row).1.1 = (coordinates middle).1.1 ∧
                (coordinates row).2 = (coordinates middle).2 := by
          change ((bankCoordinates (tailPhysicalWires ports.wires)
              (fun index => ports.qubits index.succ) row.1).2, row.2) =
            ((bankCoordinates (tailPhysicalWires ports.wires)
              (fun index => ports.qubits index.succ) middle.1).2, middle.2) ↔
              (bankCoordinates ports.wires ports.qubits row.1).1.1 =
                  (bankCoordinates ports.wires ports.qubits middle.1).1.1 ∧
                ((bankCoordinates ports.wires ports.qubits row.1).2, row.2) =
                  ((bankCoordinates ports.wires ports.qubits middle.1).2, middle.2)
          constructor
          · intro same
            have physical := congrArg Prod.fst same
            have reference := congrArg Prod.snd same
            rcases (tailBankCoordinates_complement_eq_iff
              ports.wires ports.qubits row.1 middle.1).mp physical with ⟨headSame, restSame⟩
            exact ⟨headSame, Prod.ext restSame reference⟩
          · rintro ⟨headSame, restSame⟩
            have reference : row.2 = middle.2 :=
              congrArg (fun pair :
                ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection ×
                  Reference.Index => pair.2) restSame
            exact Prod.ext
              ((tailBankCoordinates_complement_eq_iff ports.wires ports.qubits row.1 middle.1).mpr
                ⟨headSame, congrArg Prod.fst restSame⟩) reference
        refine (ih ports.tail tail row middle).trans ?_
        exact if_congr (and_congr selectedCondition remainder)
          (congrArg (fun input : Bits count => signedSourceMatrix true count tail input)
            (selected middle)) rfl
      rw [outcomeKraus, Matrix.mul_apply]
      have entries (middle : (ctx.register.prod Reference).Index) :=
        congrArg₂ (fun first second : Complex => first * second) (trailing middle)
          (window_stageKraus_source_entry ports environment Reference head middle column)
      refine (Finset.sum_congr rfl (fun middle _ => entries middle)).trans ?_
      let summand : ((Fin 2 × Bits count) ×
          (ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection ×
            Reference.Index)) → Complex := fun middle =>
        (if (coordinates row).1.2 = Partner.zeroBits count ∧
            (coordinates row).1.1 = middle.1.1 ∧ (coordinates row).2 = middle.2 then
          signedSourceMatrix true count tail middle.1.2 else 0) *
        (if middle.1.1 = 0 ∧ middle.1.2 = (coordinates column).1.2 ∧
            middle.2 = (coordinates column).2 then
          sourcePhaseWeight true count head middle.1.2 *
            Gate.HOp head (coordinates column).1.1 else 0)
      change (∑ middle : (ctx.register.prod Reference).Index, summand (coordinates middle)) = _
      refine (coordinates.sum_comp summand).trans ?_
      dsimp only [summand]
      refine (Eq.trans ?_ (retained_head_tail_sum (0 : Fin 2) (Partner.zeroBits count)
        (fun input : Bits count => signedSourceMatrix true count tail input)
        (sourcePhaseWeight true count head) (fun _ right : Fin 2 => Gate.HOp head right)
        (coordinates row) (coordinates column))).trans ?_
      · apply Finset.sum_congr rfl
        intro middle _
        apply congrArg₂ (fun first second : Complex => first * second)
        · by_cases selected : (coordinates row).1.2 = Partner.zeroBits count ∧
              (coordinates row).1.1 = middle.1.1 ∧ (coordinates row).2 = middle.2
          · simp only [if_pos selected]
          · simp only [if_neg selected]
        · by_cases selected : middle.1.1 = 0 ∧
              middle.1.2 = (coordinates column).1.2 ∧ middle.2 = (coordinates column).2
          · simp only [if_pos selected]
          · simp only [if_neg selected]
      · exact scalar_conditional_congr _ _ Iff.rfl
          (signedSourceMatrix_succ true count head
            (coordinates column).1.1 tail (coordinates column).1.2).symm

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
