/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.BankCompleteness
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.OrderedKrausWords
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Mathematics
import Mathlib.Order.Fin.Basic
import Mathlib.Data.List.OfFn

/-!
# Source-controlled ordered words of the literal complete point family

Each stage uses the actual pointBankBlock, with both complete real outcome
Stores. The mathematical source label is retained throughout the ordered
word. Its source blocks are the literal ordered bank words, and the complete
word family preserves every cross-source inner product on an arbitrary bank.

The tuples here are independent real point outcomes. Identifying them with
trace-valid full interface Store paths, adding the four conversions and the
inverse Fourier readout remain separate steps. No runtime is defined here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ControlledPointWords

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

private def mappedWord {Stage Outcome Bank : Type} [Fintype Bank]
    [bankDecision : DecidableEq Bank]
    (operators : Stage → Outcome → Matrix Bank Bank ℂ)
    (stages : List Stage) (path : Fin stages.length → Outcome) : Matrix Bank Bank ℂ :=
  OrderedKrausWords.word (stages.map operators)
    (fun index => path (Fin.cast (List.length_map (as := stages) operators) index))

private lemma mappedWord_nil {Stage Outcome Bank : Type} [Fintype Bank]
    [bankDecision : DecidableEq Bank]
    (operators : Stage → Outcome → Matrix Bank Bank ℂ) (path : Fin 0 → Outcome) :
    mappedWord operators [] path = 1 := rfl

private lemma mappedWord_cons {Stage Outcome Bank : Type} [Fintype Bank]
    [bankDecision : DecidableEq Bank]
    (operators : Stage → Outcome → Matrix Bank Bank ℂ) (stage : Stage)
    (stages : List Stage) (path : Fin (stages.length + 1) → Outcome) :
    mappedWord operators (stage :: stages) path =
      mappedWord operators stages (fun index => path index.succ) *
        operators stage (path 0) := rfl

private lemma mappedWord_complete {Stage Outcome Bank : Type}
    [Fintype Outcome] [Fintype Bank] [bankDecision : DecidableEq Bank]
    (operators : Stage → Outcome → Matrix Bank Bank ℂ) (stages : List Stage)
    (complete : ∀ stage ∈ stages,
      ∑ outcome, (operators stage outcome).conjTranspose * operators stage outcome = 1) :
    ∑ path : Fin stages.length → Outcome,
      (mappedWord operators stages path).conjTranspose * mappedWord operators stages path = 1 := by
  let paths : (Fin stages.length → Outcome) ≃
      (Fin (stages.map operators).length → Outcome) :=
    Equiv.arrowCongr
      (Fin.castOrderIso (List.length_map (as := stages) operators)).toEquiv.symm
      (Equiv.refl Outcome)
  have same (path : Fin stages.length → Outcome) :
      mappedWord operators stages path = OrderedKrausWords.word (stages.map operators)
        (paths path) := rfl
  simp only [same]
  rw [paths.sum_comp (fun path =>
    (OrderedKrausWords.word (stages.map operators)
      path).conjTranspose *
      OrderedKrausWords.word (stages.map operators) path)]
  apply OrderedKrausWords.word_complete
  intro family member
  have witness : ∃ stage : Stage, stage ∈ stages ∧ operators stage = family :=
    List.mem_map.mp member
  rcases witness with ⟨stage, present, sameFamily⟩
  subst family
  exact complete stage present

private lemma mappedWord_blockDiagonal {Stage Outcome Source Bank : Type}
    [Fintype Source] [Fintype Bank]
    [sourceDecision : DecidableEq Source] [bankDecision : DecidableEq Bank]
    (operators : Stage → Outcome → Source → Matrix Bank Bank ℂ)
    (stages : List Stage) (path : Fin stages.length → Outcome) :
    mappedWord (fun stage outcome => Matrix.blockDiagonal (operators
      stage outcome)) stages path =
      Matrix.blockDiagonal (fun source =>
        mappedWord (fun stage outcome => operators stage outcome
          source) stages path) := by
  revert path
  induction stages with
  | nil =>
      intro path
      simp only [mappedWord_nil]
      exact (Matrix.blockDiagonal_one (m := Bank) (o := Source) (α := ℂ)).symm
  | cons stage stages ih =>
      intro path
      rw [mappedWord_cons, ih]
      exact (Matrix.blockDiagonal_mul
        (fun source => mappedWord (fun stage outcome => operators
          stage outcome source)
          stages (fun index => path index.succ))
        (fun source => operators stage (path 0) source)).symm

private lemma mappedWord_submatrix {Stage Outcome Bank Other : Type}
    [Fintype Bank] [Fintype Other]
    [bankDecision : DecidableEq Bank] [otherDecision : DecidableEq Other]
    (coordinates : Other ≃ Bank) (operators : Stage → Outcome → Matrix Bank Bank ℂ)
    (stages : List Stage) (path : Fin stages.length → Outcome) :
    mappedWord (fun stage outcome =>
      (operators stage outcome).submatrix coordinates coordinates) stages path =
      (mappedWord operators stages path).submatrix coordinates
        coordinates := by
  revert path
  induction stages with
  | nil =>
      intro path
      simp only [mappedWord_nil]
      exact (Matrix.submatrix_one_equiv coordinates).symm
  | cons stage stages ih =>
      intro path
      rw [mappedWord_cons, mappedWord_cons, ih,
        Matrix.submatrix_mul_equiv _ _ coordinates coordinates coordinates]

private lemma mappedWord_chronologicalProduct {Stage Outcome Bank : Type} [Fintype Bank]
    [bankDecision : DecidableEq Bank]
    (operators : Stage → Outcome → Matrix Bank Bank ℂ)
    (stages : List Stage) (path : Fin stages.length → Outcome) :
    mappedWord operators stages path =
      QuantumFourierTransform.Semiclassical.Partner.chronologicalProduct
        (List.ofFn (fun index : Fin stages.length =>
          operators (stages.get index) (path index))) := by
  revert path
  induction stages with
  | nil => intro path; rfl
  | cons stage stages ih =>
      intro path
      rw [mappedWord_cons, ih, List.ofFn_succ,
        QuantumFourierTransform.Semiclassical.Partner.chronologicalProduct]
      rfl

/-- The outcome pair keeps the final point Store first and the division Store second. -/
abbrev Outcome (width : Nat) :=
  Store (MeasuredPointAddition.context width) × Store (MeasuredPointAddition.context width)

/-- A mathematical stage selects the actual addend and the control bit at each source. -/
abbrev Stage {p : Nat} (E : PrimeFieldShortWeierstrass p) (Source : Type) :=
  AffinePoint E × (Source → Fin 2)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (Reference : Register) {Source : Type} [Fintype Source]

/-- Every stage uses the literal full-domain source-controlled point family. -/
def word (stages : List (Stage E Source)) (path : Fin stages.length → Outcome p.size) :
    HilbertOperator (BankCompleteness.virtualRegister Source p.size Reference) :=
  mappedWord (fun stage outcome =>
    BankCompleteness.controlledBankKraus (environment := environment) E stage.1 Reference
    stage.2 outcome.2 outcome.1) stages path

/-- The bank block at one source uses the same complete real outcomes in the same order. -/
def bankWord (stages : List (Stage E Source)) (path : Fin stages.length → Outcome p.size)
    (source : Source) :
    Matrix (Recovery.Point.Instrument.FiberBank p.size Reference)
      (Recovery.Point.Instrument.FiberBank p.size Reference) ℂ :=
  mappedWord (fun stage outcome =>
    Recovery.Point.Instrument.pointBankBlock (environment := environment) E stage.1 Reference
    outcome.2 outcome.1 (stage.2 source)) stages path

attribute [local irreducible] mappedWord Recovery.Point.Instrument.pointBankBlock

omit [Fintype Source] in
/-- The exact point bank factors are in physical chronological order, with the head rightmost. -/
lemma bankWord_chronologicalProduct (stages : List (Stage E Source))
    (path : Fin stages.length → Outcome p.size) (source : Source) :
    bankWord (environment := environment) E Reference stages path source =
      QuantumFourierTransform.Semiclassical.Partner.chronologicalProduct
        (List.ofFn (fun index : Fin stages.length =>
          Recovery.Point.Instrument.pointBankBlock (environment := environment) E (stages.get
            index).1 Reference
            (path index).2 (path index).1 ((stages.get index).2 source))) := by
  unfold bankWord
  exact mappedWord_chronologicalProduct
    (Stage := Stage E Source) (Outcome := Outcome p.size)
    (Bank := Recovery.Point.Instrument.FiberBank p.size Reference)
    (fun (stage : Stage E Source) (outcome : Outcome p.size) =>
      Recovery.Point.Instrument.pointBankBlock (environment := environment) E stage.1 Reference
        outcome.2 outcome.1 (stage.2 source)) stages path

/-- The complete controlled word is exactly the direct sum of its literal bank words. -/
lemma word_blockDiagonal (stages : List (Stage E Source))
    (path : Fin stages.length → Outcome p.size) :
    word (environment := environment) E Reference stages path =
      (Matrix.blockDiagonal (fun source => bankWord (environment := environment) E Reference
        stages path source)).submatrix
        (Equiv.prodComm Source (Recovery.Point.Instrument.FiberBank p.size Reference))
        (Equiv.prodComm Source (Recovery.Point.Instrument.FiberBank p.size Reference)) := by
  let Bank := Recovery.Point.Instrument.FiberBank p.size Reference
  let coordinates : Source × Bank ≃ Bank × Source := Equiv.prodComm Source Bank
  let operators : Stage E Source → Outcome p.size → Source → Matrix Bank Bank ℂ :=
    fun stage outcome source => Recovery.Point.Instrument.pointBankBlock (environment :=
      environment) E stage.1 Reference
      outcome.2 outcome.1 (stage.2 source)
  have pulled := mappedWord_submatrix coordinates
    (fun stage outcome => Matrix.blockDiagonal (operators stage outcome)) stages path
  have blocks := mappedWord_blockDiagonal operators stages path
  have transported := congrArg
    (fun matrix : Matrix (Bank × Source) (Bank × Source) ℂ =>
      matrix.submatrix coordinates coordinates) blocks
  exact pulled.trans transported

/-- Distinct sources remain separate, including all off-diagonal bank entries. -/
lemma word_entry (stages : List (Stage E Source))
    (path : Fin stages.length → Outcome p.size) (leftSource rightSource : Source)
    (left right : Recovery.Point.Instrument.FiberBank p.size Reference) :
    word (environment := environment) E Reference stages path (leftSource, left) (rightSource,
      right) =
      if leftSource = rightSource then bankWord (environment := environment) E Reference stages
        path leftSource left right
      else 0 := by
  rw [word_blockDiagonal]
  rfl

/-- The literal point word family is complete on the entire retained free-source space. -/
lemma word_complete (stages : List (Stage E Source)) :
    ∑ path : Fin stages.length → Outcome p.size,
      (word (environment := environment) E Reference stages path).conjTranspose * word
        (environment := environment) E Reference stages path = 1 := by
  apply mappedWord_complete
    (bankDecision := (BankCompleteness.virtualRegister Source p.size Reference).decEq)
  intro stage _
  simpa only [Fintype.sum_prod_type] using
    BankCompleteness.controlledBankKraus_complete E stage.1 Reference stage.2

omit [Fintype Source] in
/-- Every individual source has the complete literal ordered bank family. -/
lemma bankWord_complete (stages : List (Stage E Source)) (source : Source) :
    ∑ path : Fin stages.length → Outcome p.size,
      (bankWord (environment := environment) E Reference stages path source).conjTranspose *
        bankWord (environment := environment) E Reference stages path source = 1 := by
  apply mappedWord_complete (Bank := Recovery.Point.Instrument.FiberBank p.size Reference)
  intro stage _
  simpa only [Fintype.sum_prod_type] using
    BankCompleteness.pointBankBlock_complete E stage.1 Reference (stage.2 source)

/-- The whole word preserves every cross-source inner product, with no support restriction. -/
lemma word_inner (stages : List (Stage E Source))
    (left right : HilbertVector (BankCompleteness.virtualRegister Source p.size Reference)) :
    ∑ path : Fin stages.length → Outcome p.size,
      inner ℂ ((word (environment := environment) E Reference stages path).applyVec left)
        ((word (environment := environment) E Reference stages path).applyVec right) = inner ℂ
          left right :=
  PointCompleteness.complete_inner
    (R := BankCompleteness.virtualRegister Source p.size Reference) (word (environment :=
      environment) E Reference stages)
    (word_complete E Reference stages) left right

/-- The free-source word dilation preserves squared norms even for zero inputs or no stages. -/
lemma word_sum_norm_sq (stages : List (Stage E Source))
    (vector : HilbertVector (BankCompleteness.virtualRegister Source p.size Reference)) :
    ∑ path : Fin stages.length → Outcome p.size,
      ‖(word (environment := environment) E Reference stages path).applyVec vector‖ ^ 2 = ‖vector‖
        ^ 2 := by
  have same := congrArg (RCLike.re (K := ℂ))
    (word_inner (environment := environment) E Reference stages vector vector)
  simpa only [map_sum, inner_self_eq_norm_sq] using same

end

end ControlledPointWords
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
