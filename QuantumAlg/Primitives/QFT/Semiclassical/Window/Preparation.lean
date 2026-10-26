/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Program
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.Head
import all QuantumAlg.Primitives.QFT.Semiclassical.Execution.SourceRows
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics
import all QuantumAlg.Core.Base.Tensor.Reference
import all QuantumAlg.Core.Execution.Interpret.Laws

/-!
# Actual Hadamards on the same recycled physical bank

The structural count induction follows the literal native H word. Its exact
matrix keeps every complementary physical coordinate and external reference.
Only the zero-column corollary assumes that the selected input bank is zero;
the caller must establish that condition at its real cleanup boundary.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution MeasurementInstrument NormalizedVector
open scoped BigOperators Kronecker

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
  {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- The actual same-wire native word extended by identity on the arbitrary reference. -/
def preparationOperator (ports : Ports ctx totalBits active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    HilbertOperator (ctx.register.prod Reference) :=
  UnitaryOperator.prodTensor ((preparation active ports).matrix environment)
    (1 : UnitaryOperator Reference)

private lemma preparationOperator_succ (ports : Ports ctx totalBits (active + 1))
    (environment : OracleModel.empty.Interpretation) (Reference : Register) :
    preparationOperator ports environment Reference =
      preparationOperator ports.tail environment Reference *
        (UnitaryOperator.prodTensor
          ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp (ports.wires 0)
            (ports.qubits 0)).matrix environment) (1 : UnitaryOperator Reference) :
              HilbertOperator (ctx.register.prod Reference)) := by
  dsimp only [preparationOperator, preparation]
  rw [UnitaryCircuit.seq_matrix, unitaryOperator_prodTensor_identity,
    unitaryOperator_prodTensor_identity, unitaryOperator_prodTensor_identity,
    HilbertOperator.kronecker_identity_mul]
  rfl

private lemma hadamard_head_tail_sum {B T R : Type} [Fintype B] [Fintype T] [Fintype R]
    (tail : T → T → Complex) (head : B → B → Complex) (row column : (B × T) × R) :
    (∑ middle : (B × T) × R,
      (if row.1.1 = middle.1.1 ∧ row.2 = middle.2 then tail row.1.2 middle.1.2 else 0) *
        (head middle.1.1 column.1.1 *
          (if middle.1.2 = column.1.2 ∧ middle.2 = column.2 then 1 else 0))) =
      if row.2 = column.2 then tail row.1.2 column.1.2 * head row.1.1 column.1.1 else 0 := by
  classical
  rw [Finset.sum_eq_single ((row.1.1, column.1.2), column.2)]
  · by_cases same : row.2 = column.2 <;> simp [same]
  · intro middle _ different
    by_cases selected : middle.1.2 = column.1.2 ∧ middle.2 = column.2
    · have excluded : ¬(row.1.1 = middle.1.1 ∧ row.2 = middle.2) := by
        intro same
        exact different (Prod.ext (Prod.ext same.1.symm selected.1) selected.2)
      simp only [if_neg excluded, zero_mul]
    · simp only [if_neg selected, mul_zero]
  · intro absent
    exact False.elim (absent (Finset.mem_univ _))

private lemma bankHadamard_succ (count : Nat) (rowHead columnHead : Fin 2)
    (rowTail columnTail : Bits count) :
    Partner.bankHadamard (count + 1) (rowHead, rowTail) (columnHead, columnTail) =
      Partner.bankHadamard count rowTail columnTail * Gate.HOp rowHead columnHead := by
  change coherentStage Gate.HOp (fun _ : Fin 2 => (1 : Matrix (Bits count) (Bits count) Complex))
    (Partner.bankHadamard count) (rowHead, rowTail) (columnHead, columnTail) = _
  have entry := phaseStage_entry Gate.HOp (fun _ : Fin 2 => fun _ : Bits count => (1 : Complex))
    (Partner.bankHadamard count) rowHead columnHead rowTail columnTail
  simpa only [Matrix.diagonal_one, mul_one] using entry

/-- The native H word has its exact selected-bank tensor matrix on the original full layout. -/
lemma window_preparation_matrix_entry (environment : OracleModel.empty.Interpretation)
    (Reference : Register) :
    ∀ (count : Nat) (ports : Ports ctx totalBits count)
      (row column : (ctx.register.prod Reference).Index),
      preparationOperator ports environment Reference row column =
        if (referenceBankCoordinates ports.wires ports.qubits Reference row).2 =
            (referenceBankCoordinates ports.wires ports.qubits Reference column).2 then
          Partner.bankHadamard count
            (referenceBankCoordinates ports.wires ports.qubits Reference row).1
            (referenceBankCoordinates ports.wires ports.qubits Reference column).1 else 0 := by
  intro count
  induction count with
  | zero =>
      intro ports row column
      let coordinates := referenceBankCoordinates ports.wires ports.qubits Reference
      have equality : row = column ↔ (coordinates row).2 = (coordinates column).2 := by
        constructor
        · intro same
          rw [same]
        · intro same
          exact coordinates.injective (Prod.ext (@Subsingleton.elim Unit inferInstance _ _) same)
      have identity :
          (UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register)
            (1 : UnitaryOperator Reference) : HilbertOperator (ctx.register.prod Reference)) =
              1 := by
        rw [unitaryOperator_prodTensor_identity]
        change (1 : HilbertOperator ctx.register) ⊗ₖ
          (1 : HilbertOperator Reference) = 1
        exact Matrix.one_kronecker_one
      change (UnitaryOperator.prodTensor (1 : UnitaryOperator ctx.register)
        (1 : UnitaryOperator Reference) : HilbertOperator (ctx.register.prod Reference))
          row column = if (coordinates row).2 = (coordinates column).2 then 1 else 0
      rw [identity]
      simp only [Matrix.one_apply, equality]
  | succ count ih =>
      intro ports row column
      let coordinates : (ctx.register.prod Reference).Index ≃
          (Fin 2 × Bits count) ×
            (ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection ×
              Reference.Index) := referenceBankCoordinates ports.wires ports.qubits Reference
      have trailing (middle : (ctx.register.prod Reference).Index) :
          preparationOperator ports.tail environment Reference row middle =
            if (coordinates row).1.1 = (coordinates middle).1.1 ∧
                (coordinates row).2 = (coordinates middle).2 then
              Partner.bankHadamard count (coordinates row).1.2 (coordinates middle).1.2 else 0 := by
        have selected (basis : (ctx.register.prod Reference).Index) :
            (referenceBankCoordinates ports.tail.wires ports.tail.qubits Reference basis).1 =
              (coordinates basis).1.2 :=
          tailBankCoordinates_selected ports.wires ports.qubits basis.1
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
              ports.wires ports.qubits row.1 middle.1).mp physical with
                ⟨headSame, restSame⟩
            exact ⟨headSame, Prod.ext restSame reference⟩
          · rintro ⟨headSame, restSame⟩
            have reference : row.2 = middle.2 :=
              congrArg (fun pair :
                ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection ×
                  Reference.Index => pair.2) restSame
            exact Prod.ext
              ((tailBankCoordinates_complement_eq_iff ports.wires ports.qubits row.1 middle.1).mpr
                ⟨headSame, congrArg Prod.fst restSame⟩) reference
        refine (ih ports.tail row middle).trans ?_
        exact if_congr remainder
          (congrArg₂ (Partner.bankHadamard count) (selected row) (selected middle)) rfl
      have leading (middle : (ctx.register.prod Reference).Index) :
          (UnitaryOperator.prodTensor
            ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp (ports.wires 0)
              (ports.qubits 0)).matrix environment) (1 : UnitaryOperator Reference))
                middle column =
            Gate.HOp (coordinates middle).1.1 (coordinates column).1.1 *
              (if (coordinates middle).1.2 = (coordinates column).1.2 ∧
                  (coordinates middle).2 = (coordinates column).2 then 1 else 0) := by
        change _ =
          Gate.HOp (bankCoordinates ports.wires ports.qubits middle.1).1.1
            (bankCoordinates ports.wires ports.qubits column.1).1.1 *
              (if (bankCoordinates ports.wires ports.qubits middle.1).1.2 =
                    (bankCoordinates ports.wires ports.qubits column.1).1.2 ∧
                  ((bankCoordinates ports.wires ports.qubits middle.1).2, middle.2) =
                    ((bankCoordinates ports.wires ports.qubits column.1).2, column.2)
                then 1 else 0)
        simpa only [Prod.mk.injEq] using
          (nativeHadamard_reference_matrix_entry ports.wires ports.qubits Reference middle column
            (environment := environment))
      rw [preparationOperator_succ, Matrix.mul_apply]
      refine (Finset.sum_congr rfl (fun middle _ =>
        congrArg₂ (fun left right : Complex => left * right)
          (trailing middle) (leading middle))).trans ?_
      let summand : ((Fin 2 × Bits count) ×
          (ctx.quantumLayout.ComplementBasis (physicalBankEmbedding ports.wires).selection ×
            Reference.Index)) → Complex := fun middle =>
        (if (coordinates row).1.1 = middle.1.1 ∧ (coordinates row).2 = middle.2 then
          Partner.bankHadamard count (coordinates row).1.2 middle.1.2 else 0) *
        (Gate.HOp middle.1.1 (coordinates column).1.1 *
          (if middle.1.2 = (coordinates column).1.2 ∧ middle.2 = (coordinates column).2
            then 1 else 0))
      change (∑ middle : (ctx.register.prod Reference).Index, summand (coordinates middle)) = _
      refine (coordinates.sum_comp summand).trans ?_
      dsimp only [summand]
      refine (Eq.trans ?_ (hadamard_head_tail_sum (Partner.bankHadamard count) Gate.HOp
        (coordinates row) (coordinates column))).trans ?_
      · apply Finset.sum_congr rfl
        intro middle _
        apply congrArg₂ (fun left right : Complex => left * right)
        · by_cases selected : (coordinates row).1.1 = middle.1.1 ∧
              (coordinates row).2 = middle.2
          · simp only [if_pos selected]
          · simp only [if_neg selected]
        · apply congrArg (fun value : Complex =>
            Gate.HOp middle.1.1 (coordinates column).1.1 * value)
          by_cases selected : middle.1.2 = (coordinates column).1.2 ∧
              middle.2 = (coordinates column).2
          · simp only [if_pos selected]
          · simp only [if_neg selected]
      · by_cases same : (coordinates row).2 = (coordinates column).2
        · have originalSame :
              (referenceBankCoordinates ports.wires ports.qubits Reference row).2 =
                (referenceBankCoordinates ports.wires ports.qubits Reference column).2 := same
          simp only [if_pos same, if_pos originalSame]
          exact (bankHadamard_succ count (coordinates row).1.1 (coordinates column).1.1
            (coordinates row).1.2 (coordinates column).1.2).symm
        · have originalDifferent :
              (referenceBankCoordinates ports.wires ports.qubits Reference row).2 ≠
                (referenceBankCoordinates ports.wires ports.qubits Reference column).2 := same
          simp only [if_neg same, if_neg originalDifferent]

/-- A genuinely zero selected input bank has the exact uniform amplitude, with full remainder. -/
lemma window_preparation_zero_column (ports : Ports ctx totalBits active)
    (environment : OracleModel.empty.Interpretation) (Reference : Register)
    (row column : (ctx.register.prod Reference).Index)
    (zero : (referenceBankCoordinates ports.wires ports.qubits Reference column).1 =
      Partner.zeroBits active) :
    preparationOperator ports environment Reference row column =
      if (referenceBankCoordinates ports.wires ports.qubits Reference row).2 =
          (referenceBankCoordinates ports.wires ports.qubits Reference column).2 then
        invSqrt2 ^ active else 0 := by
  rw [window_preparation_matrix_entry, zero, Partner.bankHadamard_zero_column]

/-- The same real H circuit preserves complete original Store, hidden state and history blocks. -/
lemma window_preparation_block_matrix (ports : Ports ctx totalBits active)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty operations
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History))
    (store : Store ctx) (hidden : services.HiddenState) (history : History) :
    (((Circuit.unitary (allowAllocation := false) (operations := operations)
      (classicalOracles := services) (preparation active ports)).execute
        environment Reference state).block (store, (hidden, (history, ())))).matrix =
      preparationOperator ports environment.quantum Reference *
        (state.block (store, (hidden, history))).matrix *
          (preparationOperator ports environment.quantum Reference).conjTranspose :=
  Circuit.execute_unitary_block_matrix environment state (preparation active ports)
    store hidden history

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
