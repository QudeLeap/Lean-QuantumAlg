/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness

/-!
# Actual middle-stage transport of the supplied point control

The all-label middle-stage identity is: the actual native word moves the original C into
the real selector N. It neither claims that physical C stays fixed nor proves the
complete point instrument's per-final-store covariance. Its native matrix law explicitly
moves an arbitrary diagonal from C to N. No clean-frame premise is used.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Control

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg
open QuantumAlg.EllipticCurve
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual controlled inverse product preserves C on every complete raw label. -/
private lemma squareStep_control_all (modulus : Nat) (state : Raw modulus.size) :
    (squareStep modulus state).1.2 = state.1.2 := by
  apply BinaryLabelEncoding.bool.encode_injective
  rw [← square_grouping_control modulus.size, ← square_grouping_control modulus.size]
  change ((squarePlacement modulus.size).grouping
      ((squarePlacement modulus.size).grouping.symm _)).1 = _
  rw [Equiv.apply_symm_apply]

/-- Exact semantic update of the literal offset/product/selector/exchange native list. -/
def middleStep {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) : Raw p.size → Raw p.size :=
  exchangeControlsStep p.size ∘
    (selectNormalStep p.size ∘
      ((squareCopyStep p.size ∘ squareStep p ∘ squareCopyStep p.size) ∘
        offsetStep p .supplied .x (constantWord (3 * Q.x))))

/-- All-label semantics of the actual middle word, without an affine or cleanliness premise. -/
lemma beforeMultiplication_realizes_all {p : Nat}
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] (Q : AffinePoint E) :
    UnitaryCircuit.Realizes (encoding p.size) (beforeMultiplication Q)
      environment.quantum (middleStep Q) :=
  nativeList_append_realizes _ _ _ _
    (nativeList_append_realizes _ _ _ _
      (nativeList_append_realizes _ _ _ _
        (offset_realizes p .supplied .x (constantWord (3 * Q.x)))
        (subtractSquare_realizes p))
      (selectNormal_realizes p.size))
    (exchangeControls_realizes p.size)

/-- During multiplication, the original supplied C resides at the actual N coordinate. -/
lemma middleStep_selector {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (Q : AffinePoint E) (state : Raw p.size) :
    (middleStep Q state).2 = state.1.2 := by
  dsimp only [middleStep, Function.comp_apply, exchangeControlsStep,
    selectNormalStep, squareCopyStep]
  rw [squareStep_control_all, offsetStep_control]

/-- Exact ket action retains the entire dirty frame, not just its C/N marginal. -/
lemma beforeMultiplication_ket_all {p : Nat}
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) (state : Raw p.size) :
    ((beforeMultiplication Q).binaryMatrix environment.quantum).apply
      (NormalizedVector.ket ((encoding p.size).encode state)) =
      NormalizedVector.ket ((encoding p.size).encode (middleStep Q state)) :=
  nativeRealizes_ket _ _ (beforeMultiplication_realizes_all Q) state

/-- Complete raw coordinates, using the existing proof that every binary label is present. -/
def rawEquiv (width : Nat) : Raw width ≃ Fin (2 ^ (encoding width).width) :=
  Equiv.ofBijective (encoding width).encode
    ⟨(encoding width).encode_injective, raw_total width⟩

/-- Arbitrary diagonal on the actual supplied C, in the native binary coordinates. -/
def controlDiagonal (width : Nat) (weight : Bool → Complex) :
    Matrix (Fin (2 ^ (encoding width).width)) (Fin (2 ^ (encoding width).width)) Complex :=
  Matrix.diagonal fun index => weight ((rawEquiv width).symm index).1.2

/-- The same arbitrary diagonal on the actual resident N, in native binary coordinates. -/
def selectorDiagonal (width : Nat) (weight : Bool → Complex) :
    Matrix (Fin (2 ^ (encoding width).width)) (Fin (2 ^ (encoding width).width)) Complex :=
  Matrix.diagonal fun index => weight ((rawEquiv width).symm index).2

/-- Actual middle matrix entries cannot mix original C with a different final N. -/
lemma beforeMultiplication_entry_support {p : Nat}
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) (input output : Raw p.size)
    (nonzero : ((beforeMultiplication Q).binaryMatrix environment.quantum)
      ((encoding p.size).encode output) ((encoding p.size).encode input) ≠ 0) :
    output.2 = input.1.2 := by
  have column := congrArg
    (fun vector : NormalizedVector (Qubits (encoding p.size).width) =>
      vector ((encoding p.size).encode output))
    (beforeMultiplication_ket_all (environment := environment) Q input)
  change ((beforeMultiplication Q).binaryMatrix environment.quantum).applyVec
    (NormalizedVector.ket ((encoding p.size).encode input)).vec
      ((encoding p.size).encode output) = _ at column
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    NormalizedVector.ket_apply] at column
  have same : (encoding p.size).encode output =
      (encoding p.size).encode (middleStep Q input) := by
    by_contra different
    rw [if_neg different] at column
    exact nonzero column
  rw [(encoding p.size).encode_injective same]
  exact middleStep_selector Q input

/-- Concrete C-to-N diagonal intertwining for the actual native middle word. -/
lemma beforeMultiplication_diagonal {p : Nat}
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) (weight : Bool → Complex) :
    (((beforeMultiplication Q).binaryMatrix environment.quantum) :
      Matrix (Fin (2 ^ (encoding p.size).width)) (Fin (2 ^ (encoding p.size).width)) Complex) *
        controlDiagonal p.size weight =
      selectorDiagonal p.size weight *
        (((beforeMultiplication Q).binaryMatrix environment.quantum) :
          Matrix (Fin (2 ^ (encoding p.size).width))
            (Fin (2 ^ (encoding p.size).width)) Complex) := by
  ext row column
  obtain ⟨input, rfl⟩ := raw_total p.size column
  obtain ⟨output, rfl⟩ := raw_total p.size row
  simp only [controlDiagonal, selectorDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
  change ((beforeMultiplication Q).binaryMatrix environment.quantum)
      ((encoding p.size).encode output) ((encoding p.size).encode input) *
        weight ((rawEquiv p.size).symm ((rawEquiv p.size) input)).1.2 =
    weight ((rawEquiv p.size).symm ((rawEquiv p.size) output)).2 *
      ((beforeMultiplication Q).binaryMatrix environment.quantum)
        ((encoding p.size).encode output) ((encoding p.size).encode input)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  by_cases zero : ((beforeMultiplication Q).binaryMatrix environment.quantum)
      ((encoding p.size).encode output) ((encoding p.size).encode input) = 0
  · rw [zero, zero_mul, mul_zero]
  · rw [beforeMultiplication_entry_support Q input output zero]
    exact mul_comm _ _

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Control
