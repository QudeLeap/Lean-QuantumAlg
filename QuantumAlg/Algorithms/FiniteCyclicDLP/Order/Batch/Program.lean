/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch.State
public import QuantumAlg.Core.Base.UnitaryCircuit.Parallel.Matrix
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Batch
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.State
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical

/-!
# Parallel native program on the fresh sample-bank family

The prefix family and its last bank form disjoint physical subsystems of the
same flat family layout.  Recursively composing the source word with the
parallel constructor exposes the product-state structure while retaining each
actual native occurrence.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderBatch

noncomputable section

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Split a nonempty flat family into its prefix and final relocated bank. -/
@[expose] public def familySnocEquiv (P : KnownOrderProblem G) (count : Nat) :
    (layout P (count + 1)).Basis ≃
      (Register.prod (layout P count).register
        ((OrderOracle.layout P).relabel (bankShift P (lastSlot count))).register).Index :=
  (familyBasisEquiv P (count + 1)).trans
    ((Fin.snocEquiv (fun _ : Fin (count + 1) => (OrderOracle.layout P).Basis)).symm.trans
      ((Equiv.prodComm _ _).trans
        (Equiv.prodCongr (familyBasisEquiv P count).symm
          (QuantumLayout.relabelBasis (OrderOracle.layout P)
            (bankShift P (lastSlot count))))))

private theorem familySnocEquiv_apply (P : KnownOrderProblem G) (count : Nat)
    (basis : (layout P (count + 1)).Basis) :
    familySnocEquiv P count basis =
      ((familyBasisEquiv P count).symm
          (fun slot => bankBasis P slot.castSucc basis),
        QuantumLayout.relabelBasis (OrderOracle.layout P)
          (bankShift P (lastSlot count))
          (bankBasis P (lastSlot count) basis)) := by
  rfl

/-- Prefix coordinates of the snoc split are the original initial banks. -/
public theorem familySnocEquiv_prefix_bank (P : KnownOrderProblem G) (count : Nat)
    (basis : (layout P (count + 1)).Basis) (slot : Fin count) :
    bankBasis P slot (familySnocEquiv P count basis).1 =
      bankBasis P slot.castSucc basis := by
  change (familyBasisEquiv P count (familySnocEquiv P count basis).1) slot = _
  rw [familySnocEquiv_apply]
  rw [(familyBasisEquiv P count).apply_symm_apply]

/-- The final coordinate of the snoc split is the original last bank. -/
public theorem familySnocEquiv_last_bank (P : KnownOrderProblem G) (count : Nat)
    (basis : (layout P (count + 1)).Basis) :
    (QuantumLayout.relabelBasis (OrderOracle.layout P)
      (bankShift P (lastSlot count))).symm (familySnocEquiv P count basis).2 =
      bankBasis P (lastSlot count) basis := by
  rw [familySnocEquiv_apply]
  rw [Equiv.symm_apply_apply]

private theorem familySnocEquiv_prefix_value (P : KnownOrderProblem G) (count : Nat)
    (basis : (layout P (count + 1)).Basis) (index : Fin (count * bankSize P)) :
    ((familySnocEquiv P count basis).1 index).val =
      (basis ((prefixEmbedding P count).position index)).val := by
  let pair := finProdFinEquiv.symm index
  have value := congrArg (fun selected : (OrderOracle.layout P).Basis =>
      (selected pair.2).val)
    (familySnocEquiv_prefix_bank P count basis pair.1)
  rw [bankBasis_value, bankBasis_value] at value
  have flattened : finProdFinEquiv (pair.1, pair.2) = index := by
    change finProdFinEquiv (finProdFinEquiv.symm index) = index
    exact Equiv.apply_symm_apply _ _
  rw [flattened] at value
  have placed : (prefixEmbedding P count).position index =
      finProdFinEquiv (pair.1.castSucc, pair.2) := by
    apply Fin.ext
    exact (congrArg Fin.val flattened).symm
  rw [placed]
  exact value

private theorem familySnocEquiv_last_value (P : KnownOrderProblem G) (count : Nat)
    (basis : (layout P (count + 1)).Basis) (index : Fin (bankSize P)) :
    ((familySnocEquiv P count basis).2 index).val =
      (basis ((bankEmbedding P (lastSlot count)).position index)).val := by
  have value := congrArg (fun selected : (OrderOracle.layout P).Basis =>
      (selected index).val) (familySnocEquiv_last_bank P count basis)
  rw [bankBasis_value] at value
  change (((QuantumLayout.relabelBasis (OrderOracle.layout P)
    (bankShift P (lastSlot count))).symm
      (familySnocEquiv P count basis).2) index).val = _
  change _ = (basis (finProdFinEquiv (lastSlot count, index))).val
  exact value

/-- The generic partition basis and the chronological bank-family split are
the same value-preserving coordinates. -/
public theorem parallelBasisEquiv_eq_familySnocEquiv
    (P : KnownOrderProblem G) (count : Nat) :
    UnitaryCircuit.parallelBasisEquiv (prefixEmbedding P count)
        (bankEmbedding P (lastSlot count)) (prefix_last_partition P count) =
      familySnocEquiv P count := by
  apply Equiv.ext
  intro basis
  apply Prod.ext
  · funext index
    apply Fin.ext
    rw [UnitaryCircuit.parallelBasisEquiv_left]
    exact (prefixEmbedding P count).embedding_splitBasis_selected_value basis index |>.trans
      (familySnocEquiv_prefix_value P count basis index).symm
  · funext index
    apply Fin.ext
    rw [UnitaryCircuit.parallelBasisEquiv_right]
    exact
      (bankEmbedding P (lastSlot count)).embedding_splitBasis_selected_value basis index |>.trans
        (familySnocEquiv_last_value P count basis index).symm

/-- The all-zero family basis splits into the all-zero prefix and final-bank
bases. -/
@[simp] public theorem familySnocEquiv_zero (P : KnownOrderProblem G) (count : Nat) :
    familySnocEquiv P count (layout P (count + 1)).zeroLabel =
      ((layout P count).zeroLabel,
        ((OrderOracle.layout P).relabel
          (bankShift P (lastSlot count))).zeroLabel) := by
  apply Prod.ext
  · funext index
    apply Fin.ext
    simpa only [QuantumLayout.zeroLabel, Fin.val_zero] using
      familySnocEquiv_prefix_value P count (layout P (count + 1)).zeroLabel index
  · funext index
    apply Fin.ext
    simpa only [QuantumLayout.zeroLabel, Fin.val_zero] using
      familySnocEquiv_last_value P count (layout P (count + 1)).zeroLabel index

/-- The recursive family word has the tensor matrix of its prefix and final
bank in the intrinsic physical partition basis. -/
public theorem familyProgram_matrix_step (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (count : Nat) :
    (familyProgram P expansion (count + 1)).matrix =
      UnitaryOperator.reindex
        (UnitaryCircuit.parallelBasisEquiv (prefixEmbedding P count)
          (bankEmbedding P (lastSlot count)) (prefix_last_partition P count)).symm
        (UnitaryOperator.prodTensor (familyProgram P expansion count).matrix
          (lastProgram P count expansion).matrix) := by
  exact UnitaryCircuit.parallel_matrix (familyProgram P expansion count)
    (lastProgram P count expansion) (prefixEmbedding P count)
    (bankEmbedding P (lastSlot count)) (prefix_last_disjoint P count)
    (prefix_last_partition P count)

private theorem lastProgram_matrix_entry (P : KnownOrderProblem G) (count : Nat)
    (expansion : OrderExpansion P.order)
    (output input : ((OrderOracle.layout P).relabel
      (bankShift P (lastSlot count))).Basis) :
    (lastProgram P count expansion).matrix output input =
      (OrderCircuit.circuit P expansion).matrix
        ((QuantumLayout.relabelBasis (OrderOracle.layout P)
          (bankShift P (lastSlot count))).symm output)
        ((QuantumLayout.relabelBasis (OrderOracle.layout P)
          (bankShift P (lastSlot count))).symm input) := by
  rw [lastProgram, UnitaryCircuit.relabel_matrix]
  rfl

/-- Acting on the all-zero family basis produces exactly the independent
product-state amplitude on every complete physical label. -/
public theorem familyProgram_zero_amplitude (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ∀ count (basis : (layout P count).Basis),
      (familyProgram P expansion count).matrix basis (layout P count).zeroLabel =
        physicalIndependentState P count expansion basis := by
  intro count
  induction count with
  | zero =>
      intro basis
      rw [physicalIndependentState_apply]
      change (if basis = (layout P 0).zeroLabel then 1 else 0) = 1
      rw [if_pos]
      funext index
      exact Fin.elim0 (Fin.cast (by simp) index)
  | succ count induction =>
      intro basis
      rw [familyProgram_matrix_step]
      simp only [UnitaryOperator.coe_reindex, Matrix.reindex_apply, Matrix.submatrix_apply]
      rw [UnitaryOperator.unitaryOperator_prodTensor_apply,
        parallelBasisEquiv_eq_familySnocEquiv]
      simp only [Equiv.symm_symm]
      rw [familySnocEquiv_zero, induction, physicalIndependentState_apply]
      rw [physicalIndependentState_apply, Fin.prod_univ_castSucc]
      apply congrArg₂ (fun left right : ℂ => left * right)
      · apply Finset.prod_congr rfl
        intro slot _
        rw [familySnocEquiv_prefix_bank]
      · rw [lastProgram_matrix_entry]
        rw [familySnocEquiv_last_bank]
        change (OrderCircuit.circuit P expansion).matrix
          (bankBasis P (lastSlot count) basis) (OrderOracle.layout P).zeroLabel = _
        unfold OrderBornBridge.evolvedState UnitaryCircuit.applyNormalized
        exact (HilbertOperator.applyVec_ket (R := (OrderOracle.layout P).register)
          (OrderCircuit.circuit P expansion).matrix
          (OrderOracle.layout P).zeroLabel
          (bankBasis P (lastSlot count) basis)).symm

/-- The complete native family word maps the all-zero preparation to the
independent physical product state. -/
public theorem familyProgram_applyNormalized_zero (P : KnownOrderProblem G)
    (count : Nat) (expansion : OrderExpansion P.order) :
    (familyProgram P expansion count).applyNormalized
        (NormalizedVector.ket (layout P count).zeroLabel) =
      physicalIndependentState P count expansion := by
  apply NormalizedVector.ext
  intro basis
  unfold UnitaryCircuit.applyNormalized
  change ((familyProgram P expansion count).matrix.applyVec
    (NormalizedVector.ket (layout P count).zeroLabel).vec) basis = _
  exact (HilbertOperator.applyVec_ket
    (familyProgram P expansion count).matrix
    (layout P count).zeroLabel basis).trans
      (familyProgram_zero_amplitude P expansion count basis)

/-- The parallel family retains exactly one copy of the source word per bank. -/
public theorem familyProgram_eventTrace (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ∀ count,
      (familyProgram P expansion count).eventTrace BitWord.model
          (ClassicalFiniteGroupOracle.model G) =
        (List.replicate count
          ((OrderCircuit.circuit P expansion).eventTrace BitWord.model
            (ClassicalFiniteGroupOracle.model G))).flatten := by
  intro count
  induction count with
  | zero => rfl
  | succ count induction =>
      change (familyProgram P expansion count).eventTrace BitWord.model
          (ClassicalFiniteGroupOracle.model G) ++
        (lastProgram P count expansion).eventTrace BitWord.model
          (ClassicalFiniteGroupOracle.model G) = _
      rw [induction]
      unfold lastProgram
      simp only [UnitaryCircuit.relabel_eventTrace]
      simp only [List.replicate_succ', List.flatten_append, List.flatten_singleton]

/-- Parallel composition preserves the total native work of every source
word. -/
public theorem familyProgram_eventCost (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ∀ count,
      (familyProgram P expansion count).eventCost BitWord.model
          (ClassicalFiniteGroupOracle.model G) =
        count • (OrderCircuit.circuit P expansion).eventCost BitWord.model
          (ClassicalFiniteGroupOracle.model G) := by
  intro count
  induction count with
  | zero => rfl
  | succ count induction =>
      change (familyProgram P expansion count).eventCost BitWord.model
          (ClassicalFiniteGroupOracle.model G) +
        (lastProgram P count expansion).eventCost BitWord.model
          (ClassicalFiniteGroupOracle.model G) = _
      rw [induction]
      unfold lastProgram
      simp only [UnitaryCircuit.relabel_eventCost, succ_nsmul]

/-- Independent banks retain one source-word critical path whenever the
family is nonempty. -/
public theorem familyProgram_unitDepth (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    ∀ count,
      DepthExpr.depthEval (fun _ => 1)
          ((familyProgram P expansion count).eventDepth BitWord.model
            (ClassicalFiniteGroupOracle.model G)) =
        if count = 0 then 0 else
          DepthExpr.depthEval (fun _ => 1)
            ((OrderCircuit.circuit P expansion).eventDepth BitWord.model
              (ClassicalFiniteGroupOracle.model G)) := by
  intro count
  induction count with
  | zero => rfl
  | succ count induction =>
      change max
        (DepthExpr.depthEval (fun _ => 1)
          ((familyProgram P expansion count).eventDepth BitWord.model
            (ClassicalFiniteGroupOracle.model G)))
        (DepthExpr.depthEval (fun _ => 1)
          ((lastProgram P count expansion).eventDepth BitWord.model
            (ClassicalFiniteGroupOracle.model G))) = _
      rw [induction]
      unfold lastProgram
      simp only [UnitaryCircuit.relabel_eventDepth]
      by_cases empty : count = 0
      · simp [empty]
      · simp [empty]

end

end QuantumAlg.FiniteCyclicDLP.OrderBatch
