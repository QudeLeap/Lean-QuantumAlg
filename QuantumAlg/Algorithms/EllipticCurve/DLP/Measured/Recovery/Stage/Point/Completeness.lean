/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Instrument.Stored
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Stored.Fibers
import all QuantumAlg.Core.Execution.Measurement.Effect
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Full-domain completeness of the literal stored point operators

The actual reset operator is an outcome-dependent unitary after a retained Z
projector and a common Hadamard unitary. The complete real Store equivalence
enumerates those projectors once, including width zero. Framing transports
their Gram identity, and the two arithmetic calls and three native unitaries
give the Gram identity of the literal five-factor point Kraus family.

All identities hold on the complete physical register with arbitrary external
Reference. No prepared-input, admissibility, normalization or cleanliness
condition is used. These are mathematical identities of the existing literal
operators; no circuit, virtual register or resource allowance is introduced.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace PointCompleteness

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma projector_decision_eq {R : Register} {Outcome : Type}
    (first second : DecidableEq Outcome) (readout : R.Index → Outcome) (outcome : Outcome) :
    @ZMeasurement.projector R Outcome first readout outcome =
      @ZMeasurement.projector R Outcome second readout outcome := by
  exact congrArg (fun choice : DecidableEq Outcome =>
    @ZMeasurement.projector R Outcome choice readout outcome) (Subsingleton.elim first second)

private lemma unitary_gram {R : Register} (operator : UnitaryOperator R) :
    (operator : HilbertOperator R).conjTranspose * (operator : HilbertOperator R) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff'.mp operator.property

private lemma unitary_sandwich_gram {R : Register} (operator : HilbertOperator R)
    (before after : UnitaryOperator R) :
    ((after : HilbertOperator R) * operator * (before : HilbertOperator R)).conjTranspose *
      ((after : HilbertOperator R) * operator * (before : HilbertOperator R)) =
      (before : HilbertOperator R).conjTranspose *
        (operator.conjTranspose * operator) * (before : HilbertOperator R) := by
  calc
    _ = (before : HilbertOperator R).conjTranspose * operator.conjTranspose *
        ((after : HilbertOperator R).conjTranspose * (after : HilbertOperator R)) *
        operator * (before : HilbertOperator R) := by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [unitary_gram, Matrix.mul_one]
      simp only [Matrix.mul_assoc]

private lemma unitary_sandwich_complete {R : Register} {Outcome : Type}
    [Fintype Outcome] (operators : Outcome → HilbertOperator R)
    (before : UnitaryOperator R) (after : Outcome → UnitaryOperator R)
    (complete : ∑ outcome, (operators outcome).conjTranspose * operators outcome = 1) :
    ∑ outcome,
      ((after outcome : HilbertOperator R) * operators outcome *
        (before : HilbertOperator R)).conjTranspose *
      ((after outcome : HilbertOperator R) * operators outcome *
        (before : HilbertOperator R)) = 1 := by
  calc
    _ = ∑ outcome, (before : HilbertOperator R).conjTranspose *
        ((operators outcome).conjTranspose * operators outcome) *
        (before : HilbertOperator R) := by
      exact Finset.sum_congr rfl fun outcome _ =>
        unitary_sandwich_gram (operators outcome) before (after outcome)
    _ = (before : HilbertOperator R).conjTranspose *
        (∑ outcome, (operators outcome).conjTranspose * operators outcome) *
        (before : HilbertOperator R) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = 1 := by rw [complete, Matrix.mul_one, unitary_gram]

private lemma projector_complete {R : Register} {Outcome : Type} [Fintype Outcome]
    (readout : R.Index → Outcome) :
    ∑ outcome, (ZMeasurement.projector readout outcome).conjTranspose *
      ZMeasurement.projector readout outcome = 1 := by
  have idempotent : ∀ outcome,
      (ZMeasurement.projector readout outcome).conjTranspose *
        ZMeasurement.projector readout outcome = ZMeasurement.projector readout outcome := by
    intro outcome
    rw [ZMeasurement.projector_conjTranspose]
    unfold ZMeasurement.projector
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext index
    split_ifs <;> simp only [one_mul, zero_mul]
  simp_rw [idempotent]
  ext row column
  by_cases same : row = column
  · subst column
    simp [Matrix.sum_apply, ZMeasurement.projector]
  · simp [Matrix.sum_apply, ZMeasurement.projector, same]

private lemma unitary_projector_complete {R : Register} {Label Outcome : Type}
    [Fintype Label] (labels : Label ≃ Outcome)
    (readout : R.Index → Outcome) (before : UnitaryOperator R)
    (after : Label → UnitaryOperator R) :
    ∑ label,
      ((after label : HilbertOperator R) * ZMeasurement.projector readout (labels label) *
        (before : HilbertOperator R)).conjTranspose *
      ((after label : HilbertOperator R) * ZMeasurement.projector readout (labels label) *
        (before : HilbertOperator R)) = 1 := by
  let _ : Fintype Outcome := Fintype.ofEquiv Label labels
  have complete : ∑ label,
      (ZMeasurement.projector readout (labels label)).conjTranspose *
        ZMeasurement.projector readout (labels label) = 1 :=
    (labels.sum_comp (fun outcome =>
      (ZMeasurement.projector readout outcome).conjTranspose *
        ZMeasurement.projector readout outcome)).trans (projector_complete (R := R) readout)
  exact unitary_sandwich_complete (R := R)
    (fun label => ZMeasurement.projector readout (labels label)) before after complete

private lemma unitary_projector_family_complete {R : Register} {Label Outcome : Type}
    [Fintype Label] (operators : Label → HilbertOperator R) (labels : Label ≃ Outcome)
    (readout : R.Index → Outcome) (before : UnitaryOperator R)
    (after : Label → UnitaryOperator R)
    (factor : ∀ label, operators label =
      (after label : HilbertOperator R) * ZMeasurement.projector readout (labels label) *
        (before : HilbertOperator R)) :
    ∑ label, (operators label).conjTranspose * operators label = 1 := by
  calc
    _ = ∑ label,
        ((after label : HilbertOperator R) * ZMeasurement.projector readout (labels label) *
          (before : HilbertOperator R)).conjTranspose *
        ((after label : HilbertOperator R) * ZMeasurement.projector readout (labels label) *
          (before : HilbertOperator R)) := by
      apply Finset.sum_congr rfl
      intro label _
      rw [factor]
    _ = 1 := unitary_projector_complete (R := R) labels readout before after

section ResetCompleteness

attribute [local irreducible] NumeratorRuntime.program NumeratorReset.member
  NumeratorReset.hadamardMember

private def resetBefore (width : Nat) (Reference : Register) :
    UnitaryOperator ((NumeratorMeasurement.context width).register.prod Reference) :=
  UnitaryOperator.prodTensor
    ((NumeratorRuntime.program width (NumeratorReset.hadamardMember width)).matrix
      environment.quantum)
    (1 : UnitaryOperator Reference)

private def resetAfter (width : Nat) (Reference : Register)
    (stored : Store (NumeratorMeasurement.context width)) :
    UnitaryOperator ((NumeratorMeasurement.context width).register.prod Reference) :=
  UnitaryOperator.prodTensor
    ((NumeratorRuntime.program width
      (NumeratorReset.member width (stored.read (NumeratorMeasurement.input width)))).matrix
        environment.quantum)
    (1 : UnitaryOperator Reference)

private def resetReadout (width : Nat) (Reference : Register) :
    ((NumeratorMeasurement.context width).register.prod Reference).Index → Fin (2 ^ width) :=
  fun entry => NumeratorObservation.word width entry.1

private lemma reset_operator_factor (width : Nat) (Reference : Register)
    (stored : Store (NumeratorMeasurement.context width)) :
    NumeratorResetConjugation.operator environment.quantum width Reference stored =
      (resetAfter (environment := environment) width Reference stored :
        HilbertOperator ((NumeratorMeasurement.context width).register.prod Reference)) *
      ZMeasurement.projector (resetReadout width Reference)
        ((NumeratorStoredFibers.outcomeEquiv width) stored) *
      (resetBefore (environment := environment) width Reference :
        HilbertOperator ((NumeratorMeasurement.context width).register.prod Reference)) := by
  unfold NumeratorResetConjugation.operator resetAfter resetBefore resetReadout
  rfl

attribute [local irreducible] resetBefore resetAfter resetReadout
  NumeratorResetConjugation.operator NumeratorStoredFibers.outcomeEquiv

/-- Every real retained reset Store occurs exactly once in the full Gram sum. -/
lemma reset_complete (width : Nat) (Reference : Register) :
    ∑ stored : Store (NumeratorMeasurement.context width),
      (NumeratorResetConjugation.operator environment.quantum width Reference
        stored).conjTranspose *
        NumeratorResetConjugation.operator environment.quantum width Reference stored = 1 := by
  exact unitary_projector_family_complete
    (R := Register.prod (NumeratorMeasurement.context width).register Reference)
    (Label := Store (NumeratorMeasurement.context width)) (Outcome := Fin (2 ^ width))
    (NumeratorResetConjugation.operator environment.quantum width Reference)
    (NumeratorStoredFibers.outcomeEquiv width) (resetReadout width
      Reference)
    (resetBefore (environment := environment) width Reference) (resetAfter (environment :=
      environment) width Reference)
    (fun stored => by
      refine (reset_operator_factor width Reference stored).trans ?_
      apply congrArg
        (fun projector :
            HilbertOperator ((NumeratorMeasurement.context width).register.prod Reference) =>
          (resetAfter (environment := environment) width Reference stored :
            HilbertOperator ((NumeratorMeasurement.context width).register.prod Reference)) *
              projector * (resetBefore (environment := environment) width Reference :
                HilbertOperator ((NumeratorMeasurement.context width).register.prod Reference)))
      exact projector_decision_eq _ _ (resetReadout width Reference)
        ((NumeratorStoredFibers.outcomeEquiv width) stored))

end ResetCompleteness

private lemma reindexed_complete {R S : Register} {Outcome : Type} [Fintype Outcome]
    (coordinates : R.Index ≃ S.Index) (operators : Outcome → HilbertOperator S)
    (complete : ∑ outcome, (operators outcome).conjTranspose * operators outcome = 1) :
    ∑ outcome, ((operators outcome).submatrix coordinates coordinates).conjTranspose *
      (operators outcome).submatrix coordinates coordinates = 1 := by
  calc
    _ = (∑ outcome, (operators outcome).conjTranspose * operators outcome).submatrix
        coordinates coordinates := by
      ext row column
      simp only [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
        Matrix.sum_apply, Matrix.submatrix_apply]
    _ = (1 : HilbertOperator S).submatrix coordinates coordinates := by rw [complete]
    _ = 1 := Matrix.submatrix_one_equiv coordinates

/-- Adding the real control frame preserves the unrestricted reset Gram identity. -/
lemma framed_reset_complete (width : Nat) (Reference : Register) :
    ∑ stored : Store (InPlaceControlled.context width),
      (InPlaceControlled.framedResetOperator environment.quantum width Reference
        stored).conjTranspose *
        InPlaceControlled.framedResetOperator environment.quantum width Reference stored = 1 := by
  let coordinates := ContextUnion.referenceBasis (NumeratorMeasurement.context width)
    (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width) Reference
  let operators := NumeratorResetConjugation.operator environment.quantum width
    (Register.prod (InPlaceControlled.controlContext width).register Reference)
  have complete := reindexed_complete coordinates operators
    (reset_complete width (Register.prod (InPlaceControlled.controlContext width).register
      Reference))
  rw [← (InPlaceControlled.storeCoordinates width).sum_comp
    (fun stored => ((operators stored).submatrix coordinates coordinates).conjTranspose *
      (operators stored).submatrix coordinates coordinates)] at complete
  exact complete

/-- The actual stored suffix may depend arbitrarily on its outcome without changing completeness.
-/
lemma controlled_complete (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register) :
    ∑ stored : Store (InPlaceControlled.context modulus.size),
      (InPlaceControlled.actualOperator environment.quantum operation modulus prime Reference
        stored).conjTranspose *
        InPlaceControlled.actualOperator environment.quantum operation modulus prime Reference
          stored = 1 := by
  exact unitary_sandwich_complete
    (InPlaceControlled.framedResetOperator environment.quantum modulus.size Reference)
    (InPlaceControlled.nativeJoint environment.quantum modulus.size Reference
      (InPlaceControlled.beforeReset operation modulus prime))
    (fun stored => InPlaceControlled.nativeJoint environment.quantum modulus.size Reference
      (InPlaceControlled.suffix operation modulus prime
        (stored.read (InPlaceControlled.resultInput modulus.size))))
    (framed_reset_complete modulus.size Reference)

/-- Pullback through the real selector frame keeps the complete arithmetic CP family. -/
lemma arithmetic_complete (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register) :
    ∑ stored : Store (MeasuredPointAddition.context modulus.size),
      (Recovery.Point.Instrument.arithmeticOperator (environment := environment) operation modulus
        prime Reference
        stored).conjTranspose *
        Recovery.Point.Instrument.arithmeticOperator (environment := environment) operation
          modulus prime Reference stored =
          1 := by
  let coordinates := ContextUnion.referenceBasis (InPlaceControlled.context modulus.size)
    (MeasuredPointAddition.selectorContext modulus.size)
    (MeasuredPointAddition.selector_disjoint modulus.size) Reference
  let operators := InPlaceControlled.actualOperator environment.quantum operation modulus prime
    (Register.prod (MeasuredPointAddition.selectorContext modulus.size).register Reference)
  have complete := reindexed_complete coordinates operators
    (controlled_complete operation modulus prime
      (Register.prod (MeasuredPointAddition.selectorContext modulus.size).register Reference))
  rw [← (Recovery.Point.Instrument.storeCoordinates modulus.size).sum_comp
    (fun stored => ((operators stored).submatrix coordinates coordinates).conjTranspose *
      (operators stored).submatrix coordinates coordinates)] at complete
  exact complete

private lemma composition_complete {R : Register} {First Second : Type}
    [Fintype First] [Fintype Second] (first : First → HilbertOperator R)
    (second : Second → HilbertOperator R)
    (firstComplete : ∑ outcome, (first outcome).conjTranspose * first outcome = 1)
    (secondComplete : ∑ outcome, (second outcome).conjTranspose * second outcome = 1) :
    ∑ final, ∑ initial, (second final * first initial).conjTranspose *
      (second final * first initial) = 1 := by
  rw [Finset.sum_comm]
  calc
    _ = ∑ initial, (first initial).conjTranspose *
        (∑ final, (second final).conjTranspose * second final) * first initial := by
      apply Finset.sum_congr rfl
      intro initial _
      simp only [Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]
    _ = ∑ initial, (first initial).conjTranspose * first initial := by
      simp only [secondComplete, Matrix.mul_one]
    _ = 1 := firstComplete

private lemma five_factor_complete {R : Register} {First Second : Type}
    [Fintype First] [Fintype Second] (first : First → HilbertOperator R)
    (second : Second → HilbertOperator R) (before middle after : UnitaryOperator R)
    (firstComplete : ∑ initial, (first initial).conjTranspose * first initial = 1)
    (secondComplete : ∑ final, (second final).conjTranspose * second final = 1) :
    ∑ final, ∑ initial,
      ((after : HilbertOperator R) * second final * (middle : HilbertOperator R) *
        first initial * (before : HilbertOperator R)).conjTranspose *
      ((after : HilbertOperator R) * second final * (middle : HilbertOperator R) *
        first initial * (before : HilbertOperator R)) = 1 := by
  let firstWord : First → HilbertOperator R := fun initial =>
    (middle : HilbertOperator R) * first initial * (before : HilbertOperator R)
  let secondWord : Second → HilbertOperator R := fun final =>
    (after : HilbertOperator R) * second final * (1 : HilbertOperator R)
  have firstWordComplete : ∑ initial,
      (firstWord initial).conjTranspose * firstWord initial = 1 :=
    unitary_sandwich_complete (R := R) first before (fun _ => middle) firstComplete
  have secondWordComplete : ∑ final,
      (secondWord final).conjTranspose * secondWord final = 1 :=
    unitary_sandwich_complete (R := R) second (1 : UnitaryOperator R)
      (fun _ => after) secondComplete
  have complete := composition_complete (R := R) firstWord secondWord
    firstWordComplete secondWordComplete
  simpa only [firstWord, secondWord, Matrix.mul_one, Matrix.mul_assoc] using complete

/-- The literal two-outcome point family is complete on every physical input column. -/
lemma pointKraus_complete {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register) :
    ∑ finalStore : Store (MeasuredPointAddition.context p.size),
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
          divisionStore
          finalStore).conjTranspose *
          Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
            divisionStore finalStore = 1 := by
  let R := Register.prod (MeasuredPointAddition.context p.size).register Reference
  let before : UnitaryOperator R :=
    MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
      (MeasuredPointAddition.beforeDivision Q)
  let middle : UnitaryOperator R := MeasuredPointAddition.nativeJoint (environment := environment)
    p.size Reference
    (MeasuredPointAddition.beforeMultiplication Q)
  let after : UnitaryOperator R := MeasuredPointAddition.nativeJoint (environment := environment)
    p.size Reference
    (MeasuredPointAddition.afterMultiplication E Q)
  let division : Store (MeasuredPointAddition.context p.size) → HilbertOperator R :=
    Recovery.Point.Instrument.arithmeticOperator (environment := environment) .division p Fact.out
      Reference
  let multiplication : Store (MeasuredPointAddition.context p.size) → HilbertOperator R :=
    Recovery.Point.Instrument.arithmeticOperator (environment := environment) .multiplication p
      Fact.out Reference
  have factorization (divisionStore finalStore : Store (MeasuredPointAddition.context p.size)) :
      Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
        divisionStore finalStore =
        (after : HilbertOperator R) * multiplication finalStore * (middle : HilbertOperator R) *
          division divisionStore * (before : HilbertOperator R) := rfl
  calc
    _ = ∑ finalStore : Store (MeasuredPointAddition.context p.size),
        ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
          ((after : HilbertOperator R) * multiplication finalStore *
            (middle : HilbertOperator R) * division divisionStore *
            (before : HilbertOperator R)).conjTranspose *
          ((after : HilbertOperator R) * multiplication finalStore *
            (middle : HilbertOperator R) * division divisionStore *
            (before : HilbertOperator R)) := by
      apply Finset.sum_congr rfl
      intro finalStore _
      apply Finset.sum_congr rfl
      intro divisionStore _
      rw [factorization]
    _ = 1 := five_factor_complete (R := R) division multiplication before middle after
      (arithmetic_complete .division p Fact.out Reference)
      (arithmetic_complete .multiplication p Fact.out Reference)

private lemma inner_gram {R : Register} (operator : HilbertOperator R)
    (left right : HilbertVector R) :
    inner ℂ (operator.applyVec left) (operator.applyVec right) =
      inner ℂ left (HilbertOperator.applyVec (operator.conjTranspose * operator) right) := by
  change inner ℂ (Matrix.toEuclideanLin operator left) (Matrix.toEuclideanLin operator right) =
    inner ℂ left (Matrix.toEuclideanLin (operator.conjTranspose * operator) right)
  rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.comp_apply, LinearMap.adjoint_inner_right]

private lemma complete_inner {R : Register} {Outcome : Type} [Fintype Outcome]
    (operators : Outcome → HilbertOperator R)
    (complete : ∑ outcome, (operators outcome).conjTranspose * operators outcome = 1)
    (left right : HilbertVector R) :
    ∑ outcome, inner ℂ ((operators outcome).applyVec left)
      ((operators outcome).applyVec right) = inner ℂ left right := by
  calc
    _ = ∑ outcome, inner ℂ left
        (HilbertOperator.applyVec
          ((operators outcome).conjTranspose * operators outcome) right) := by
      exact Finset.sum_congr rfl fun outcome _ => inner_gram (operators outcome) left right
    _ = inner ℂ left
        (HilbertOperator.applyVec
          (∑ outcome, (operators outcome).conjTranspose * operators outcome) right) := by
      rw [HilbertOperator.sum_applyVec, inner_sum]
    _ = inner ℂ left right := by rw [complete, HilbertOperator.one_applyVec]

/-- Cross-input inner products are preserved after summing both actual stored outcomes. -/
lemma pointKraus_inner {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (left right : HilbertVector (Register.prod (MeasuredPointAddition.context p.size).register
      Reference)) :
    ∑ finalStore : Store (MeasuredPointAddition.context p.size),
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        inner ℂ ((Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
          divisionStore
          finalStore).applyVec left)
          ((Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
            divisionStore
            finalStore).applyVec right) =
      inner ℂ left right := by
  let operators := fun stored : Store (MeasuredPointAddition.context p.size) ×
      Store (MeasuredPointAddition.context p.size) =>
    Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference stored.2
      stored.1
  have complete : ∑ outcome, (operators outcome).conjTranspose * operators outcome = 1 := by
    simpa only [operators, Fintype.sum_prod_type] using pointKraus_complete E Q Reference
  simpa only [operators, Fintype.sum_prod_type] using complete_inner operators complete left right

/-- The full literal point instrument preserves the squared norm of every unrestricted vector. -/
lemma pointKraus_sum_norm_sq {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (vector : HilbertVector (Register.prod (MeasuredPointAddition.context p.size).register
      Reference)) :
    ∑ finalStore : Store (MeasuredPointAddition.context p.size),
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        ‖(Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
          divisionStore finalStore).applyVec
          vector‖ ^ 2 =
      ‖vector‖ ^ 2 := by
  have same := congrArg (RCLike.re (K := ℂ))
    (pointKraus_inner (environment := environment) E Q Reference vector vector)
  simpa only [map_sum, inner_self_eq_norm_sq] using same

/-- The CP family preserves the trace of every matrix, without a positivity or mass premise. -/
lemma pointKraus_trace {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (matrix : HilbertOperator (Register.prod (MeasuredPointAddition.context p.size).register
      Reference)) :
    (∑ finalStore : Store (MeasuredPointAddition.context p.size),
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
          divisionStore finalStore * matrix *
          (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
            divisionStore
            finalStore).conjTranspose).trace =
      matrix.trace := by
  simp only [Matrix.trace_sum]
  calc
    _ = ∑ finalStore : Store (MeasuredPointAddition.context p.size),
        ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
          (((Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
            divisionStore
            finalStore).conjTranspose *
            Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
              divisionStore finalStore) *
              matrix).trace := by
      apply Finset.sum_congr rfl
      intro finalStore _
      apply Finset.sum_congr rfl
      intro divisionStore _
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc]
    _ = ((∑ finalStore : Store (MeasuredPointAddition.context p.size),
        ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
          (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
            divisionStore
            finalStore).conjTranspose *
            Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
              divisionStore finalStore) *
              matrix).trace := by
      simp only [Matrix.sum_mul, Matrix.trace_sum]
    _ = matrix.trace := by rw [pointKraus_complete, Matrix.one_mul]

end

end PointCompleteness
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
