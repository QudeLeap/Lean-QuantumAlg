/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.Completeness
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Point.Fibers
import all Mathlib.Data.Matrix.Block

/-!
# Full-domain bank completeness and a retained mathematical source label

The literal point family does not leak between its two control fibers on any
bank input. This full-domain fact, rather than a good-input support theorem,
allows its complete Gram identity to descend to either fixed-control bank.
The finite source label below is only a mathematical direct sum. Each source
selects its own control bit, and all source coordinates, including their
coherences, remain in the same complete Gram identity. No register is allocated
by a circuit and no resource claim or actual whole-path identification is made.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace BankCompleteness

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

-- Keep full operator implementations opaque during the finite matrix algebra below.
attribute [local irreducible] Recovery.Point.Instrument.pointKraus
  Recovery.Point.Instrument.pointBankBlock Recovery.Point.Instrument.fiberBasis

private lemma pointKraus_gram_fiber_entry {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (Reference : Register)
    (divisionStore finalStore : Store (MeasuredPointAddition.context p.size))
    (bit : Fin 2) (left right : Recovery.Point.Instrument.FiberBank p.size Reference) :
    ((Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
      divisionStore finalStore).conjTranspose *
      Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
        divisionStore finalStore)
      ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm (bit, left))
      ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm (bit, right)) =
      ((Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
        divisionStore finalStore
        bit).conjTranspose *
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
          divisionStore finalStore bit)
          left right := by
  let coordinates :
      (Register.prod (MeasuredPointAddition.context p.size).register Reference).Index ≃
        Fin 2 × Recovery.Point.Instrument.FiberBank p.size Reference :=
    Recovery.Point.Instrument.fiberBasis p.size Reference
  let operator : HilbertOperator
      (Register.prod (MeasuredPointAddition.context p.size).register Reference) :=
    Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference divisionStore
      finalStore
  change (∑ output, star (operator output (coordinates.symm (bit, left))) *
    operator output (coordinates.symm (bit, right))) = _
  calc
    _ = ∑ bank : Recovery.Point.Instrument.FiberBank p.size Reference,
        star (operator (coordinates.symm (bit, bank)) (coordinates.symm (bit, left))) *
          operator (coordinates.symm (bit, bank)) (coordinates.symm (bit, right)) := by
      rw [← coordinates.symm.sum_comp (fun output =>
        star (operator output (coordinates.symm (bit, left))) *
          operator output (coordinates.symm (bit, right))), Fintype.sum_prod_type]
      apply Finset.sum_eq_single bit
      · intro other _ different
        apply Finset.sum_eq_zero
        intro bank _
        change star (Recovery.Point.Instrument.pointKraus (environment := environment) E Q
          Reference divisionStore finalStore
          ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm (other, bank))
          ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm (bit, left))) * _ = 0
        rw [Recovery.Point.Instrument.pointKraus_fiber_entry, if_neg different, star_zero, zero_mul]
      · intro absent
        exact (absent (Finset.mem_univ bit)).elim
    _ = _ := by
      dsimp only [operator, coordinates]
      simp only [Recovery.Point.Instrument.pointKraus_fiber_entry, if_true,
        Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Either complete control fiber has its own trace-preserving bank CP family. -/
lemma pointBankBlock_complete {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) (bit : Fin 2) :
    ∑ finalStore : Store (MeasuredPointAddition.context p.size),
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        (Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
          divisionStore finalStore
          bit).conjTranspose *
          Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
            divisionStore finalStore bit =
            1 := by
  ext left right
  let coordinates := Recovery.Point.Instrument.fiberBasis p.size Reference
  have entry := congrArg (fun matrix : HilbertOperator
      (Register.prod (MeasuredPointAddition.context p.size).register Reference) =>
    matrix (coordinates.symm (bit, left)) (coordinates.symm (bit, right)))
    (PointCompleteness.pointKraus_complete (environment := environment) E Q Reference)
  simp only [Matrix.sum_apply] at entry
  change (∑ finalStore : Store (MeasuredPointAddition.context p.size),
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        ((Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
          divisionStore
          finalStore).conjTranspose *
          Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
            divisionStore finalStore)
          ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm (bit, left))
          ((Recovery.Point.Instrument.fiberBasis p.size Reference).symm (bit, right))) = _ at entry
  simp only [pointKraus_gram_fiber_entry] at entry
  have identityEntry :
      (1 : HilbertOperator
        (Register.prod (MeasuredPointAddition.context p.size).register Reference))
        (coordinates.symm (bit, left)) (coordinates.symm (bit, right)) =
        (1 : Matrix (Recovery.Point.Instrument.FiberBank p.size Reference)
          (Recovery.Point.Instrument.FiberBank p.size Reference) ℂ) left right := by
    by_cases same : left = right
    · subst right
      simp only [Matrix.one_apply]
    · have different : coordinates.symm (bit, left) ≠ coordinates.symm (bit, right) := by
        intro equal
        exact same (congrArg Prod.snd (coordinates.symm.injective equal))
      simp only [Matrix.one_apply, if_neg same, if_neg different]
  simpa only [Matrix.sum_apply] using entry.trans identityEntry

/-- A proof-only direct sum retains a finite virtual source and the entire physical bank. -/
def virtualRegister (Source : Type) [Fintype Source] (width : Nat) (Reference : Register) :
    Register where
  Index := Source × Recovery.Point.Instrument.FiberBank width Reference
  fintype := inferInstance
  decEq := inferInstance

/-- The same real outcomes label all source-controlled blocks, with the source retained. -/
def controlledBankKraus {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) {Source : Type} [Fintype Source]
    (control : Source → Fin 2)
    (divisionStore finalStore : Store (MeasuredPointAddition.context p.size)) :
    HilbertOperator (virtualRegister Source p.size Reference) :=
  (Matrix.blockDiagonal (fun source =>
    Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
      divisionStore finalStore
      (control source))).submatrix
      (Equiv.prodComm Source (Recovery.Point.Instrument.FiberBank p.size Reference))
      (Equiv.prodComm Source (Recovery.Point.Instrument.FiberBank p.size Reference))

/-- Distinct virtual sources stay orthogonal for arbitrary bank entries. -/
lemma controlledBankKraus_entry {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) {Source : Type} [Fintype Source]
    (control : Source → Fin 2)
    (divisionStore finalStore : Store (MeasuredPointAddition.context p.size))
    (leftSource rightSource : Source) (left right : Recovery.Point.Instrument.FiberBank p.size
      Reference) :
    controlledBankKraus (environment := environment) E Q Reference control divisionStore finalStore
      (leftSource, left) (rightSource, right) =
      if leftSource = rightSource then
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
          divisionStore finalStore
          (control leftSource) left right
      else 0 := rfl

private lemma blockDiagonal_complete {Bank Source Outcome : Type}
    [Fintype Bank] [Fintype Source] [Fintype Outcome]
    [DecidableEq Bank] [DecidableEq Source]
    (blocks : Outcome → Source → Matrix Bank Bank ℂ)
    (complete : ∀ source, ∑ outcome,
      (blocks outcome source).conjTranspose * blocks outcome source = 1) :
    ∑ outcome, (Matrix.blockDiagonal (blocks outcome)).conjTranspose *
      Matrix.blockDiagonal (blocks outcome) = 1 := by
  have familyComplete : (∑ outcome, fun source =>
      (blocks outcome source).conjTranspose * blocks outcome source) = 1 := by
    funext source
    simpa only [Finset.sum_apply, Pi.one_apply] using complete source
  calc
    _ = ∑ outcome, Matrix.blockDiagonal (fun source =>
        (blocks outcome source).conjTranspose * blocks outcome source) := by
      apply Finset.sum_congr rfl
      intro outcome _
      rw [Matrix.blockDiagonal_conjTranspose, ← Matrix.blockDiagonal_mul]
    _ = Matrix.blockDiagonal (∑ outcome, fun source =>
        (blocks outcome source).conjTranspose * blocks outcome source) := by
      let hom := Matrix.blockDiagonalAddMonoidHom
        (m := Bank) (n := Bank) (o := Source) (α := ℂ)
      change (∑ outcome, hom (fun source =>
        (blocks outcome source).conjTranspose * blocks outcome source)) =
          hom (∑ outcome, fun source =>
            (blocks outcome source).conjTranspose * blocks outcome source)
      exact (map_sum hom _ Finset.univ).symm
    _ = 1 := by rw [familyComplete, Matrix.blockDiagonal_one]

/-- The mathematical controlled family is complete on the full free-source space. -/
lemma controlledBankKraus_complete {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (Reference : Register) {Source : Type} [Fintype Source]
    (control : Source → Fin 2) :
    ∑ finalStore : Store (MeasuredPointAddition.context p.size),
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        (controlledBankKraus (environment := environment) E Q Reference control divisionStore
          finalStore).conjTranspose *
          controlledBankKraus (environment := environment) E Q Reference control divisionStore
            finalStore = 1 := by
  let Bank := Recovery.Point.Instrument.FiberBank p.size Reference
  let Outcome := Store (MeasuredPointAddition.context p.size) ×
    Store (MeasuredPointAddition.context p.size)
  let blocks : Outcome → Source → Matrix Bank Bank ℂ := fun outcome source =>
    Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference outcome.2
      outcome.1 (control source)
  have blockComplete (source : Source) : ∑ outcome : Outcome,
      (blocks outcome source).conjTranspose * blocks outcome source = 1 := by
    change (∑ outcome : Store (MeasuredPointAddition.context p.size) ×
        Store (MeasuredPointAddition.context p.size),
      (Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
        outcome.2 outcome.1
        (control source)).conjTranspose *
        Recovery.Point.Instrument.pointBankBlock (environment := environment) E Q Reference
          outcome.2 outcome.1 (control
          source)) = 1
    rw [Fintype.sum_prod_type]
    exact pointBankBlock_complete E Q Reference (control source)
  let LabelLast : Register :=
    { Index := Bank × Source, fintype := inferInstance, decEq := inferInstance }
  have complete : ∑ outcome : Outcome,
      (Matrix.blockDiagonal (blocks outcome) : HilbertOperator LabelLast).conjTranspose *
        Matrix.blockDiagonal (blocks outcome) = 1 :=
    blockDiagonal_complete blocks blockComplete
  have pulled := PointCompleteness.reindexed_complete
    (R := virtualRegister Source p.size Reference) (S := LabelLast)
    (Equiv.prodComm Source Bank) (fun outcome : Outcome => Matrix.blockDiagonal (blocks outcome))
    complete
  rw [Fintype.sum_prod_type] at pulled
  exact pulled

/-- Free-source vectors retain their cross inner products under the same actual outcome family. -/
lemma controlledBankKraus_inner {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) {Source : Type} [Fintype Source]
    (control : Source → Fin 2)
    (left right : HilbertVector (virtualRegister Source p.size Reference)) :
    ∑ finalStore : Store (MeasuredPointAddition.context p.size),
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        inner ℂ ((controlledBankKraus (environment := environment) E Q Reference control
          divisionStore finalStore).applyVec left)
          ((controlledBankKraus (environment := environment) E Q Reference control divisionStore
            finalStore).applyVec right) =
      inner ℂ left right := by
  let operators := fun stored : Store (MeasuredPointAddition.context p.size) ×
      Store (MeasuredPointAddition.context p.size) =>
    controlledBankKraus (environment := environment) E Q Reference control stored.2 stored.1
  have complete : ∑ outcome, (operators outcome).conjTranspose * operators outcome = 1 := by
    simpa only [operators, Fintype.sum_prod_type] using
      controlledBankKraus_complete E Q Reference control
  simpa only [operators, Fintype.sum_prod_type] using
    PointCompleteness.complete_inner operators complete left right

/-- The retained-source dilation is norm-preserving for every unrestricted coherent input. -/
lemma controlledBankKraus_sum_norm_sq {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (Reference : Register) {Source : Type} [Fintype Source]
    (control : Source → Fin 2)
    (vector : HilbertVector (virtualRegister Source p.size Reference)) :
    ∑ finalStore : Store (MeasuredPointAddition.context p.size),
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        ‖(controlledBankKraus (environment := environment) E Q Reference control divisionStore
          finalStore).applyVec vector‖ ^ 2 =
      ‖vector‖ ^ 2 := by
  have same := congrArg (RCLike.re (K := ℂ))
    (controlledBankKraus_inner (environment := environment) E Q Reference control vector vector)
  simpa only [map_sum, inner_self_eq_norm_sq] using same

end

end BankCompleteness
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
