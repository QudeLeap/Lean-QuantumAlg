/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Instrument.Stored
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Correctness

/-!
# Common coherent columns of every actual measured point outcome

The literal point Kraus matrix used by the fixed false point body has the
same scalar on every original admissible complete column. The scalar is
independent of the input, both controls, the reference and the two stored
outcomes. Its cross-column products therefore retain every relative phase.

Only low-level native operator and controlled measured-column contracts are
used. No old scalar compiler or true point-body execution is invoked. The
admissible support below is a local mathematical domain to establish from
the original good-source trajectory, not a new public input certificate.
The whole streaming source Gram identity and free-source contraction remain
separate obligations.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
namespace Instrument.GoodColumns

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
open QuantumAlg.Execution.ContextUnion
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

private lemma controlled_column (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register)
    (stored : Store (InPlaceControlled.context modulus.size))
    (input row : ((InPlaceControlled.context modulus.size).register.prod Reference).Index)
    (allowed : InPlaceControlled.admissible modulus input.1) :
    InPlaceControlled.actualOperator environment.quantum operation modulus prime Reference stored
      row input =
      WalshHadamard.invSqrtCard modulus.size *
        InPlaceControlled.target operation modulus prime Reference row input := by
  obtain ⟨input, reference⟩ := input
  obtain ⟨control, value, numerator, rfl, domain⟩ := allowed
  rw [InPlaceControlled.actualOperator_blocks]
  exact InPlaceControlled.prepared_column operation modulus prime control value numerator
    domain (InPlaceControlled.storeCoordinates modulus.size stored) reference row

/-- The actual selector pullback preserves the common column scalar and every reference entry. -/
lemma arithmeticOperator_column (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register)
    (stored : Store (context modulus.size))
    (input row : ((context modulus.size).register.prod Reference).Index)
    (allowed : InPlaceControlled.admissible modulus
      ((unionBasisEquiv (InPlaceControlled.context modulus.size) (selectorContext modulus.size)
        (selector_disjoint modulus.size) input.1).1)) :
    arithmeticOperator (environment := environment) operation modulus prime Reference stored row
      input =
      WalshHadamard.invSqrtCard modulus.size *
        arithmeticTarget operation modulus prime Reference row input := by
  let coordinates := referenceBasis (InPlaceControlled.context modulus.size)
    (selectorContext modulus.size) (selector_disjoint modulus.size) Reference
  change InPlaceControlled.admissible modulus (coordinates input).1 at allowed
  change InPlaceControlled.actualOperator environment.quantum operation modulus prime
      ((selectorContext modulus.size).register.prod Reference)
      (Recovery.Point.Instrument.storeCoordinates modulus.size stored) (coordinates row)
        (coordinates input) =
    WalshHadamard.invSqrtCard modulus.size *
      InPlaceControlled.target operation modulus prime
        ((selectorContext modulus.size).register.prod Reference)
        (coordinates row) (coordinates input)
  exact controlled_column operation modulus prime _ _ _ _ allowed

private lemma arithmeticOperator_ket (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register)
    (stored : Store (context modulus.size))
    (input : ((context modulus.size).register.prod Reference).Index)
    (allowed : InPlaceControlled.admissible modulus
      ((unionBasisEquiv (InPlaceControlled.context modulus.size) (selectorContext modulus.size)
        (selector_disjoint modulus.size) input.1).1)) :
    HilbertOperator.applyVec (arithmeticOperator (environment := environment) operation modulus
      prime Reference stored)
        (NormalizedVector.ket input).vec =
      WalshHadamard.invSqrtCard modulus.size •
        (arithmeticTarget operation modulus prime Reference).applyVec
          (NormalizedVector.ket input).vec := by
  apply WithLp.ofLp_injective
  funext row
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  change HilbertOperator.applyVec _ (NormalizedVector.ket input).vec row =
    WalshHadamard.invSqrtCard modulus.size *
      HilbertOperator.applyVec _ (NormalizedVector.ket input).vec row
  rw [HilbertOperator.applyVec_ket, HilbertOperator.applyVec_ket]
  exact arithmeticOperator_column operation modulus prime Reference stored input row allowed

/-- Every actual division/final outcome has one common scalar on all allowed full columns. -/
lemma pointKraus_column {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (divisionStore finalStore : Store (context p.size))
    (input row : ((context p.size).register.prod Reference).Index)
    (allowed : MeasuredPointAddition.admissible E Q input.1) :
    pointKraus (environment := environment) E Q Reference divisionStore finalStore row input =
      (WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size) *
        target E Q Reference row input := by
  let R := (context p.size).register.prod Reference
  let before : HilbertOperator R :=
    nativeJoint (environment := environment) p.size Reference (beforeDivision Q)
  let middle : HilbertOperator R :=
    nativeJoint (environment := environment) p.size Reference (beforeMultiplication Q)
  let after : HilbertOperator R :=
    nativeJoint (environment := environment) p.size Reference (afterMultiplication E Q)
  let division : HilbertOperator R := arithmeticTarget .division p Fact.out Reference
  let multiplication : HilbertOperator R := arithmeticTarget .multiplication p Fact.out Reference
  let divided : HilbertOperator R := arithmeticOperator (environment := environment) .division p
    Fact.out Reference divisionStore
  let multiplied : HilbertOperator R :=
    arithmeticOperator (environment := environment) .multiplication p Fact.out Reference finalStore
  let scalar := WalshHadamard.invSqrtCard p.size
  obtain ⟨first, firstAllowed, firstReached⟩ :=
    first_arithmetic_reachable (environment := environment) E Q input allowed
  obtain ⟨second, secondAllowed, secondReached⟩ :=
    second_arithmetic_reachable (environment := environment) E Q input allowed
  change HilbertOperator.applyVec before (NormalizedVector.ket input).vec =
    (NormalizedVector.ket first).vec at firstReached
  change HilbertOperator.applyVec (middle * division * before)
    (NormalizedVector.ket input).vec = (NormalizedVector.ket second).vec at secondReached
  have firstAction : HilbertOperator.applyVec divided (NormalizedVector.ket first).vec =
      scalar • HilbertOperator.applyVec division (NormalizedVector.ket first).vec :=
    arithmeticOperator_ket .division p Fact.out Reference divisionStore first firstAllowed
  have secondAction : HilbertOperator.applyVec multiplied (NormalizedVector.ket second).vec =
      scalar • HilbertOperator.applyVec multiplication (NormalizedVector.ket second).vec :=
    arithmeticOperator_ket .multiplication p Fact.out Reference finalStore second secondAllowed
  have reaches : HilbertOperator.applyVec middle
      (HilbertOperator.applyVec division (NormalizedVector.ket first).vec) =
        (NormalizedVector.ket second).vec := by
    simpa only [HilbertOperator.mul_applyVec, firstReached] using secondReached
  have targetAction : HilbertOperator.applyVec after
      (HilbertOperator.applyVec multiplication (NormalizedVector.ket second).vec) =
        (target E Q Reference).applyVec (NormalizedVector.ket input).vec := by
    calc
      _ = HilbertOperator.applyVec (after * multiplication * middle * division * before)
          (NormalizedVector.ket input).vec := by
        simp only [HilbertOperator.mul_applyVec, firstReached, reaches]
      _ = _ := by
        apply WithLp.ofLp_injective
        funext output
        change HilbertOperator.applyVec _ (NormalizedVector.ket input).vec output =
          HilbertOperator.applyVec _ (NormalizedVector.ket input).vec output
        rw [HilbertOperator.applyVec_ket, HilbertOperator.applyVec_ket]
        exact executionOperator_target_columns E Q input allowed output
  have action : HilbertOperator.applyVec (pointKraus (environment := environment) E Q Reference
    divisionStore finalStore)
      (NormalizedVector.ket input).vec =
        (scalar * scalar) • (target E Q Reference).applyVec
          (NormalizedVector.ket input).vec := by
    change HilbertOperator.applyVec (after * multiplied * middle * divided * before)
      (NormalizedVector.ket input).vec = _
    simp only [HilbertOperator.mul_applyVec, firstReached, firstAction,
      HilbertOperator.applyVec_smul, reaches, secondAction, targetAction, smul_smul]
  have entry := congrArg (fun vector : HilbertVector R => vector row) action
  simpa only [HilbertOperator.applyVec_ket, UnitaryOperator.applyVec,
    PiLp.smul_apply, smul_eq_mul] using entry

/-- Different admissible input columns retain the same outcome phase in their full cross kernel. -/
lemma pointKraus_cross_column {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (divisionStore finalStore : Store (context p.size))
    (left right row column : ((context p.size).register.prod Reference).Index)
    (leftAllowed : MeasuredPointAddition.admissible E Q left.1)
    (rightAllowed : MeasuredPointAddition.admissible E Q right.1) :
    pointKraus (environment := environment) E Q Reference divisionStore finalStore row left *
        star (pointKraus (environment := environment) E Q Reference divisionStore finalStore
          column right) =
      let scalar := WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size
      (scalar * star scalar) *
        (target E Q Reference row left * star (target E Q Reference column right)) := by
  rw [pointKraus_column E Q Reference divisionStore finalStore left row leftAllowed,
    pointKraus_column E Q Reference divisionStore finalStore right column rightAllowed]
  dsimp only
  rw [star_mul]
  ring

/-- Every supported density keeps arbitrary mixed and off-diagonal reference coherences. -/
lemma pointKraus_supported_sandwich {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (divisionStore finalStore : Store (context p.size))
    (density : DensityOperator ((context p.size).register.prod Reference))
    (support : ∀ input, ¬MeasuredPointAddition.admissible E Q input.1 →
      density.matrix input input = 0) :
    pointKraus (environment := environment) E Q Reference divisionStore finalStore *
      density.matrix *
        (pointKraus (environment := environment) E Q Reference divisionStore
          finalStore).conjTranspose =
      let scalar := WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size
      (scalar * star scalar) •
        ((target E Q Reference : HilbertOperator _) * density.matrix *
          (target E Q Reference : HilbertOperator _).conjTranspose) := by
  let scalar := WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size
  have agrees := DensityOperator.conjugation_eq_on_basis_support density
    (fun input => MeasuredPointAddition.admissible E Q input.1)
    (pointKraus (environment := environment) E Q Reference divisionStore finalStore)
    (scalar • (target E Q Reference : HilbertOperator _)) support
    (fun input allowed row => pointKraus_column E Q Reference divisionStore finalStore
      input row allowed)
  exact agrees.trans (by
    simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm (star scalar) scalar])

/-- The two actual complete Store outcome sets have exactly the required scalar mass. -/
lemma point_outcome_coefficient_sum (width : Nat) :
    (∑ _division : Store (context width), ∑ _final : Store (context width),
      let scalar := WalshHadamard.invSqrtCard width * WalshHadamard.invSqrtCard width
      scalar * star scalar) = (1 : ℂ) := by
  have oneCall := InPlaceControlled.coefficient_normalized width
  have storeCard := Fintype.card_congr (Recovery.Point.Instrument.storeCoordinates width)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [storeCard]
  rw [star_mul]
  calc
    _ = ((Fintype.card (Store (InPlaceControlled.context width)) : ℂ) *
        (WalshHadamard.invSqrtCard width * star (WalshHadamard.invSqrtCard width))) *
        ((Fintype.card (Store (InPlaceControlled.context width)) : ℂ) *
          (WalshHadamard.invSqrtCard width * star (WalshHadamard.invSqrtCard width))) := by ring
    _ = 1 := by simp only [oneCall, one_mul]

/-- Summing both actual outcome Stores gives the full independent point channel on its domain. -/
lemma pointKraus_supported_sum {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (density : DensityOperator ((context p.size).register.prod Reference))
    (support : ∀ input, ¬MeasuredPointAddition.admissible E Q input.1 →
      density.matrix input input = 0) :
    (∑ division : Store (context p.size), ∑ final : Store (context p.size),
      pointKraus (environment := environment) E Q Reference division final * density.matrix *
        (pointKraus (environment := environment) E Q Reference division final).conjTranspose) =
      (target E Q Reference : HilbertOperator _) * density.matrix *
        (target E Q Reference : HilbertOperator _).conjTranspose := by
  simp_rw [pointKraus_supported_sandwich E Q Reference _ _ density support]
  calc
    _ = (∑ _division : Store (context p.size), ∑ _final : Store (context p.size),
        let scalar := WalshHadamard.invSqrtCard p.size * WalshHadamard.invSqrtCard p.size
        scalar * star scalar) •
        ((target E Q Reference : HilbertOperator _) * density.matrix *
          (target E Q Reference : HilbertOperator _).conjTranspose) := by
      simp only [Finset.sum_smul]
    _ = _ := by rw [point_outcome_coefficient_sum, one_smul]

/-- The literal false point body has this full coherent channel on the internally proved domain. -/
lemma fixed_pointBody_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) {Reference : Register} {History : Type} [Fintype History]
    (state : State (context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (support : ∀ input : ((context p.size).register.prod Reference).Index,
      ¬MeasuredPointAddition.admissible E Q input.1 →
        state.quantumMarginal.matrix input input = 0) :
    ((Recovery.Point.pointBody E Q).execute environment Reference state).quantumMarginal =
      DensityOperator.applyUnitary (target E Q Reference) state.quantumMarginal := by
  apply DensityOperator.ext
  rw [DensityOperator.applyUnitary_matrix,
    ← Execution.sum_store_matrices ((Recovery.Point.pointBody E Q).execute environment Reference
      state)]
  calc
    _ = ∑ final : Store (context p.size), ∑ division : Store (context p.size),
        pointKraus (environment := environment) E Q Reference division final *
          state.quantumMarginal.matrix *
          (pointKraus (environment := environment) E Q Reference division final).conjTranspose := by
      apply Finset.sum_congr rfl
      intro final _
      exact Recovery.Point.pointBody_store_matrix E Q state final
    _ = _ := by
      rw [Finset.sum_comm]
      exact pointKraus_supported_sum E Q Reference state.quantumMarginal support

end

end Instrument.GoodColumns
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
