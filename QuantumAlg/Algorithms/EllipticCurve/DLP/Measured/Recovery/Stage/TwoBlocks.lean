/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Path.Word
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.WordRecursion
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Rows
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Program
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback

/-!
# Two actual exponent blocks with their genuine memory-zero continuation

Complete Store, dirty bank, arbitrary external Reference and original arithmetic factor
order are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord.TwoBlocks

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open StoredRecursion
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private abbrev Interface (width m : Nat) := Recovery.Layout.terminal width m

lemma two_blocks_original_order (m : Nat) :
    blockIndices (m := m) false m le_rfl ++ blockIndices true m le_rfl = Recovery.Layout.order
      m := by
  rw [blockIndices_original_order, blockIndices_original_order]
  unfold Recovery.Layout.order
  apply List.ext_getElem
  · simp only [List.length_append, List.length_map, List.length_finRange]
    omega
  · intro position leftBound rightBound
    by_cases first : position < m
    · rw [List.getElem_append_left (by
        simpa only [List.length_map, List.length_finRange] using first)]
      simp only [List.getElem_map, List.getElem_finRange, Bool.false_eq_true, ↓reduceIte]
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_castAdd]
    · rw [List.getElem_append_right (by
        simpa only [List.length_map, List.length_finRange] using Nat.le_of_not_lt first)]
      simp only [List.getElem_map, List.getElem_finRange, ↓reduceIte,
        List.length_map, List.length_finRange]
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_natAdd]
      omega

private lemma pathProduct_append {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (first second : List (Fin (2 * m))) :
    pathProduct (environment := environment) E r points Reference division intermediate outcomes
      (first ++ second) =
      pathProduct (environment := environment) E r points Reference division intermediate outcomes
        second *
        pathProduct (environment := environment) E r points Reference division intermediate
          outcomes first := by
  induction first with
  | nil => simp only [List.nil_append, pathProduct, Matrix.mul_one]
  | cons index tail ih =>
      simp only [List.cons_append, pathProduct, ih, Matrix.mul_assoc]

private lemma freshBlock_continuation {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension) (indices : List (Fin (2 * m)))
    (continuation : Matrix ((Interface p.size m).register.prod Reference).Index
      ((Interface p.size m).register.prod Reference).Index ℂ) :
    freshBlock Reference
        (continuation * pathProduct (environment := environment) E r points Reference division
          intermediate outcomes indices) =
      freshBlock Reference continuation *
        freshBlock Reference (pathProduct (environment := environment) E r points Reference
          division intermediate
          outcomes indices) := by
  induction indices generalizing continuation with
  | nil => simp only [pathProduct, Matrix.mul_one, freshBlock_one]
  | cons index tail ih =>
      simp only [pathProduct]
      rw [← Matrix.mul_assoc, freshBlock_tail_stage, ih, freshBlock_tail_stage, Matrix.mul_assoc]

private lemma path_memory_one_zero {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (second : Bool)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension) (positive : 0 < r) (fits : r ≤ 2 ^ m) :
    memoryBlock (freshBlock Reference (pathProduct (environment := environment) E r points
      Reference division intermediate
      outcomes (blockIndices second m le_rfl))) true false = 0 := by
  change (freshBlock Reference (pathProduct (environment := environment) E r points Reference
    division intermediate
    outcomes (blockIndices second m le_rfl))).submatrix (Prod.mk true) (Prod.mk false) = 0
  rw [actual_path_initialized_sum E r points Reference second division intermediate outcomes
    positive fits true]
  simp only [Bool.true_eq_false, and_false, if_false, Complex.ofReal_zero, zero_smul,
    Finset.sum_const_zero]

private lemma two_blocks_memory_factorization {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (positive : 0 < r) (fits : r ≤ 2 ^ m) (final : Bool) :
    (freshBlock Reference (pathProduct (environment := environment) E r points Reference division
      intermediate outcomes
        (Recovery.Layout.order m))).submatrix (Prod.mk final) (Prod.mk false) =
      (freshBlock Reference (pathProduct (environment := environment) E r points Reference
        division intermediate outcomes
        (blockIndices true m le_rfl))).submatrix (Prod.mk final) (Prod.mk false) *
      (freshBlock Reference (pathProduct (environment := environment) E r points Reference
        division intermediate outcomes
        (blockIndices false m le_rfl))).submatrix (Prod.mk false) (Prod.mk false) := by
  rw [← two_blocks_original_order, pathProduct_append, freshBlock_continuation]
  change memoryBlock
      (freshBlock Reference (pathProduct (environment := environment) E r points Reference
        division intermediate outcomes
          (blockIndices true m le_rfl)) *
        freshBlock Reference (pathProduct (environment := environment) E r points Reference
          division intermediate outcomes
          (blockIndices false m le_rfl))) final false = _
  rw [memoryBlock_mul, Fintype.sum_bool,
    path_memory_one_zero E r points Reference false division intermediate outcomes positive fits,
    Matrix.mul_zero, zero_add]
  rfl

lemma actual_two_block_words {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (division : Fin (2 * m) → Store (MeasuredPointAddition.context p.size))
    (intermediate : Fin (2 * m) → Store (Interface p.size m))
    (outcomes : Fin (2 * m) → Fin ((Interface p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (positive : 0 < r) (fits : r ≤ 2 ^ m) (final : Bool) :
    (freshBlock Reference (pathProduct (environment := environment) E r points Reference division
      intermediate outcomes
        (Recovery.Layout.order m))).submatrix (Prod.mk final) (Prod.mk false) =
      ∑ secondWord ∈ Finset.range (2 ^ m), ∑ firstWord ∈ Finset.range (2 ^ m),
        (((if secondWord < r ∧ final = false then invSqrt r else 0 : ℝ) : ℂ) *
          ((if firstWord < r then invSqrt r else 0 : ℝ) : ℂ)) •
          OrderedBankWord.exponentPair
            (blockAction (environment := environment)
              E points Reference false division intermediate outcomes)
            (blockAction (environment := environment)
              E points Reference true division intermediate outcomes)
            m firstWord secondWord := by
  rw [two_blocks_memory_factorization E r points Reference division intermediate outcomes
    positive fits final]
  rw [actual_path_initialized_sum E r points Reference true division intermediate outcomes
    positive fits final,
    actual_path_initialized_sum E r points Reference false division intermediate outcomes
      positive fits false]
  simp only [and_true, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul,
    Finset.smul_sum, smul_smul, OrderedBankWord.exponentPair]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro secondWord _
  apply Finset.sum_congr rfl
  intro firstWord _
  rw [mul_comm (G := ℂ)]

end

end PointCoordinates.StageWord.PathWord.TwoBlocks
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
