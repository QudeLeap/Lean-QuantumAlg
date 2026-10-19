/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all
  QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Common.Cascade
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Store.Coordinates
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Fourier.WordFactor
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases

/-!
# The actual old ordered bank word and the streaming arithmetic word

A new complete branch constructs the old ready Store by the complete bare-terminal
equivalence, the old terminal-cell split and the original body permutation. The division
label is copied verbatim. Every old point factor then equals the corresponding new
factor after the explicit bank-basis pullback, at arbitrary dirty Store values.

The increasing-index word is split into its first and second chronological
lists, so the second bank word multiplies the first. No arithmetic matrices
commute. External Reference and both control blocks remain arbitrary, and
m = 0 is included. The new readout outcome is not identified with an old
arithmetic outcome, nor is this branch map claimed injective. Actual valid-path
fibers, deferred terminal writes, CP multiplicities, Fourier/native exponent
coordinates, conversion factors and common positive output states are separate
obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout
namespace BankWords

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.QuantumFourierTransform QuantumFourierTransform.Semiclassical
open ScalarMultiplication.MeasuredPlacement
open Recovery.Stage.PointCoordinates

open Recovery.Stage.PointCoordinates.StageWord.PathWord
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The old ready Store is constructed from the entire new terminal Store. -/
def oldReadyStore (modulus m : Nat) (stored : Store (Recovery.Layout.terminal modulus.size m)) :
    Store (readyContext modulus.size (2 * m)) :=
  (ContextPermutation.storeEquiv (Allocation.body_entries modulus.size (2 * m))).symm
    (Recovery.Reference.Terminal.cellStoreEquiv (Allocation.after modulus.size (2 * m)) 2 (2 * m)
      (BareStores.terminal modulus m stored)).1

/-- Every indexed old call sees the same complete point Store as the actual new factor. -/
lemma oldReadyStore_pointStore (modulus m : Nat) (active : Fin (2 * m))
    (stored : Store (Recovery.Layout.terminal modulus.size m)) :
    (Recovery.Reference.Measured.pointStore modulus.size active (oldReadyStore modulus m
      stored)).1 =
      Recovery.Layout.Reference.streamingPointStore modulus.size m stored := by
  change Recovery.Point.Store.oldTerminalPointStore modulus m active
    (BareStores.terminal modulus m stored) = _
  exact Recovery.Point.Store.terminal_pointStore modulus m active stored

/-- The full new stored label determines the old branch; its division label is untouched. -/
def oldBranch (modulus m : Nat) (branch : PathDensity.Branch modulus.size m) :
    Recovery.Reference.Measured.Branch modulus.size (2 * m) :=
  (oldReadyStore modulus m branch.1, branch.2.2)

lemma oldBranch_division (modulus m : Nat) (branch : PathDensity.Branch modulus.size m) :
    (oldBranch modulus m branch).2 = branch.2.2 := rfl

/-- One literal point factor, with the same full stored point label and division outcome. -/
lemma bankBlock_oldBranch {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (Q : AffinePoint E) (active : Fin (2 * m)) (Reference : Register)
    (branch : PathDensity.Branch p.size m) (control : Fin 2) :
    (bankBlock (environment := environment) E Q m Reference branch.2.2 branch.1 control).submatrix
        (Recovery.Layout.Reference.bankBasis p.size m Reference).symm
        (Recovery.Layout.Reference.bankBasis p.size m Reference).symm =
      Recovery.Reference.Measured.CommonBank.bankKraus (environment := environment) E Q active
        Reference
        (oldBranch p m branch).2 (oldBranch p m branch).1 control := by
  rw [Recovery.Layout.Reference.bankBlock_common]
  change Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
    branch.2.2
      (Recovery.Layout.Reference.streamingPointStore p.size m branch.1) control =
    Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference branch.2.2
      (Recovery.Reference.Measured.pointStore p.size active (oldReadyStore p m branch.1)).1 control
  rw [oldReadyStore_pointStore]

/-- A complete path supplies one constructed old branch at each original index. -/
def oldPath (modulus m length : Nat) (path : Fin length → PathDensity.Branch modulus.size m) :
    Fin length → Recovery.Reference.Measured.Branch modulus.size (2 * m) :=
  fun current => oldBranch modulus m (path current)

/-- The existing old recurrence is exactly a chronological list of its original factors. -/
lemma bankWord_chronological {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register)
    (length : Nat) (indices : Fin length → Fin count)
    (path : Fin length → Recovery.Reference.Measured.Branch p.size count)
    (exponent : Recovery.Reference.Measured.CommonBank.Exponents count) :
    Recovery.Reference.Measured.CommonBank.bankWord (environment := environment) E points
      Reference length indices path
      exponent =
      Partner.chronologicalProduct (List.ofFn (fun current : Fin length =>
        Recovery.Reference.Measured.CommonBank.bankKraus (environment := environment) E (points
          (indices current)) (indices
          current) Reference
          (path current).2 (path current).1 (exponent (indices current)))) := by
  induction length with
  | zero =>
      simp only [Recovery.Reference.Measured.CommonBank.bankWord, List.ofFn_zero,
        Partner.chronologicalProduct]
  | succ length ih =>
      simp only [Recovery.Reference.Measured.CommonBank.bankWord, List.ofFn_succ,
        Partner.chronologicalProduct]
      exact congrArg (fun matrix => matrix *
        Recovery.Reference.Measured.CommonBank.bankKraus (environment := environment) E (points
          (indices 0)) (indices 0)
          Reference
          (path 0).2 (path 0).1 (exponent (indices 0)))
        (ih (Fin.tail indices) (Fin.tail path))

private lemma chronological_submatrix {B C : Type} [Fintype B] [Fintype C]
    [DecidableEq B] [DecidableEq C] (basis : B ≃ C) (items : List (Matrix B B ℂ)) :
    (Partner.chronologicalProduct items).submatrix basis.symm basis.symm =
      Partner.chronologicalProduct
        (items.map (fun matrix => matrix.submatrix basis.symm basis.symm)) := by
  induction items with
  | nil => simp only [Partner.chronologicalProduct, List.map_nil, Matrix.submatrix_one_equiv]
  | cons head tail ih =>
      simp only [Partner.chronologicalProduct, List.map_cons]
      rw [← Matrix.submatrix_mul_equiv _ _ basis.symm basis.symm basis.symm, ih]

/-- The actual new point factors in arbitrary original index order. -/
def streamingWord {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (length : Nat) (indices : Fin length → Fin (2 * m))
    (path : Fin length → PathDensity.Branch p.size m)
    (exponent : Recovery.Reference.Measured.CommonBank.Exponents (2 * m)) :
    Matrix (Bank p.size m Reference) (Bank p.size m Reference) ℂ :=
  Partner.chronologicalProduct (List.ofFn (fun current : Fin length =>
    bankBlock (environment := environment) E (points (indices current)) m Reference (path
      current).2.2
      (path current).1 (exponent (indices current))))

/-- The actual old bankWord equals the pulled-back original list of new point factors. -/
lemma streamingWord_old_bankWord {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (length : Nat) (indices : Fin length → Fin (2 * m))
    (path : Fin length → PathDensity.Branch p.size m)
    (exponent : Recovery.Reference.Measured.CommonBank.Exponents (2 * m)) :
    (streamingWord (environment := environment) E points Reference length indices path
      exponent).submatrix
        (Recovery.Layout.Reference.bankBasis p.size m Reference).symm
        (Recovery.Layout.Reference.bankBasis p.size m Reference).symm =
      Recovery.Reference.Measured.CommonBank.bankWord (environment := environment) E points
        Reference length indices
        (oldPath p m length path) exponent := by
  rw [streamingWord, chronological_submatrix, List.map_ofFn, bankWord_chronological]
  apply congrArg Partner.chronologicalProduct
  apply congrArg List.ofFn
  funext current
  exact bankBlock_oldBranch E (points (indices current)) (indices current) Reference
    (path current) (exponent (indices current))

private lemma chronological_append {B : Type} [Fintype B] [DecidableEq B]
    (first second : List (Matrix B B ℂ)) :
    Partner.chronologicalProduct (first ++ second) =
      Partner.chronologicalProduct second * Partner.chronologicalProduct first := by
  induction first with
  | nil => simp only [List.nil_append, Partner.chronologicalProduct, mul_one]
  | cons head tail ih =>
      simp only [List.cons_append, Partner.chronologicalProduct, ih, Matrix.mul_assoc]

/-- The physical paired exponent function, with both tuples in their original MSB order. -/
def pairedExponent (m : Nat) (first second : Bits m) :
  Recovery.Reference.Measured.CommonBank.Exponents (2 * m) :=
  fun index => Fin.append (tupleCoordinates m first) (tupleCoordinates m second)
    (Fin.cast (Nat.two_mul m) index)

lemma pairedExponent_position_false (m : Nat) (first second : Bits m) (current : Fin m) :
    pairedExponent m first second (ActualFeedback.position false current) =
      tupleCoordinates m first current := by
  simp only [pairedExponent, ActualFeedback.position, StageWord.blockIndex_original_order,
    Bool.false_eq_true, ↓reduceIte]
  change Fin.append (tupleCoordinates m first) (tupleCoordinates m second)
    (Fin.castAdd m current) = _
  exact Fin.append_left _ _ _

lemma pairedExponent_position_true (m : Nat) (first second : Bits m) (current : Fin m) :
    pairedExponent m first second (ActualFeedback.position true current) =
      tupleCoordinates m second current := by
  simp only [pairedExponent, ActualFeedback.position, StageWord.blockIndex_original_order,
    ↓reduceIte]
  change Fin.append (tupleCoordinates m first) (tupleCoordinates m second)
    (Fin.natAdd m current) = _
  exact Fin.append_right _ _ _

private lemma ofFn_two_blocks {A : Type} (m : Nat) (items : Fin (2 * m) → A) :
    List.ofFn items =
      List.ofFn (fun current : Fin m => items (ActualFeedback.position false current)) ++
        List.ofFn (fun current : Fin m => items (ActualFeedback.position true current)) := by
  rw [List.ofFn_congr (Nat.two_mul m) items, List.ofFn_add]
  simp only [ActualFeedback.position, StageWord.blockIndex_original_order,
    Bool.false_eq_true, ↓reduceIte]
  rfl

/-- The in-range path action is the same real point factor for both control values. -/
lemma pathBankAction_in_range {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → PathDensity.Branch p.size m) (second : Bool) (remaining : Fin m)
    (control : Fin 2) :
    ActualFeedback.pathBankAction (environment := environment) E points Reference path second
      remaining.val
        (finTwoEquiv control) =
      bankBlock (environment := environment) E (points (StageWord.blockIndex second remaining)) m
        Reference
        (path (StageWord.blockIndex second remaining)).2.2
        (path (StageWord.blockIndex second remaining)).1 control := by
  simp only [ActualFeedback.pathBankAction, dif_pos remaining.isLt]
  fin_cases control <;> rfl

private lemma chronological_block_tupleWord {p : Nat}
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → PathDensity.Branch p.size m) (second : Bool) (input : Bits m) :
    Partner.chronologicalProduct (List.ofFn (fun current : Fin m =>
      bankBlock (environment := environment) E (points (ActualFeedback.position second current)) m
        Reference
        (path (ActualFeedback.position second current)).2.2
        (path (ActualFeedback.position second current)).1 (tupleCoordinates m input current))) =
      FourierWord.tupleWord m
        (ActualFeedback.pathBankAction (environment := environment) E points Reference path
          second) input := by
  unfold FourierWord.tupleWord
  apply congrArg Partner.chronologicalProduct
  apply congrArg List.ofFn
  funext current
  exact (pathBankAction_in_range E points Reference path second current.rev
    (tupleCoordinates m input current)).symm

/-- Increasing old point indices are exactly first-then-second streaming MSB words. -/
lemma streamingWord_exponentPair {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → PathDensity.Branch p.size m) (first second : Bits m) :
    streamingWord (environment := environment) E points Reference (2 * m) id path (pairedExponent
      m first second) =
      OrderedBankWord.exponentPair
        (ActualFeedback.pathBankAction (environment := environment) E points Reference path false)
        (ActualFeedback.pathBankAction (environment := environment) E points Reference path true)
        m (binaryEquiv m first).val (binaryEquiv m second).val := by
  unfold streamingWord
  rw [ofFn_two_blocks, chronological_append]
  simp only [id_eq, pairedExponent_position_false, pairedExponent_position_true]
  rw [chronological_block_tupleWord, chronological_block_tupleWord]
  rw [OrderedBankWord.exponentPair, FourierWord.word_eq_tupleWord,
    FourierWord.word_eq_tupleWord]

/-- Exact actual-old/new arithmetic bank-word identity on arbitrary dirty stored labels. -/
lemma old_bankWord_eq_exponentPair {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (path : Fin (2 * m) → PathDensity.Branch p.size m) (first second : Bits m) :
    Recovery.Reference.Measured.CommonBank.bankWord (environment := environment) E points
      Reference (2 * m) id (oldPath p m
      (2 * m) path)
        (pairedExponent m first second) =
      (OrderedBankWord.exponentPair
        (ActualFeedback.pathBankAction (environment := environment) E points Reference path false)
        (ActualFeedback.pathBankAction (environment := environment) E points Reference path true)
        m (binaryEquiv m first).val (binaryEquiv m second).val).submatrix
        (Recovery.Layout.Reference.bankBasis p.size m Reference).symm
        (Recovery.Layout.Reference.bankBasis p.size m Reference).symm := by
  rw [← streamingWord_exponentPair]
  exact (streamingWord_old_bankWord E points Reference (2 * m) id path
    (pairedExponent m first second)).symm

end

end BankWords
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Layout
