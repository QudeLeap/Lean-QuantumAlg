/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Instrument.Stored
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Control.Transport
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Measured.Correctness
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Controlled.Correctness

/-!
# Original point Kraus fibers on the complete dirty bank

Complete Store, dirty bank, arbitrary external Reference and original arithmetic factor
order are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Control

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.Execution.ContextUnion
open QuantumAlg.EllipticCurve
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private lemma exceptionalOffset_control_all (modulus : Nat) (coordinate : Coordinate)
    (constant : Fin (modulus + 1)) (state : Raw modulus.size) :
    (offsetStep modulus .exceptional coordinate constant state).1.2 = state.1.2 :=
  offsetStep_preserves_bit modulus .exceptional coordinate constant state (controlBit modulus.size)
    (control_outside_coordinate modulus.size coordinate)

private lemma reflectStep_control_all (modulus : Nat) (state : Raw modulus.size) :
    (reflectStep modulus state).1.2 = state.1.2 := by
  apply BinaryLabelEncoding.bool.encode_injective
  rw [← grouping_suppliedControl modulus.size .x,
    ← grouping_suppliedControl modulus.size .x]
  change ((offsetPlacement modulus.size .supplied .x).grouping
    ((offsetPlacement modulus.size .supplied .x).grouping.symm _)).1 = _
  rw [Equiv.apply_symm_apply]

lemma afterMultiplication_control_all {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (state : Raw p.size) :
    (afterMultiplicationStep E Q state).1.2 = state.2 := by
  dsimp only [afterMultiplicationStep, Function.comp_apply]
  rw [offsetStep_control, offsetStep_control, reflectStep_control_all]
  change (offsetStep p .exceptional .y (constantWord (-exceptionalSlope E Q))
    (exchangeControlsStep p.size state)).1.2 = state.2
  rw [exceptionalOffset_control_all]
  rfl

private lemma native_readout_support {width : Nat} (program : NativeCircuit width)
    (action : Raw width → Raw width)
    (realized : UnitaryCircuit.Realizes (encoding width) program environment.quantum action)
    (before after : Raw width → Bool) (readout : ∀ state, after (action state) = before state)
    (input output : Raw width)
    (nonzero : (program.binaryMatrix environment.quantum) ((encoding width).encode output)
      ((encoding width).encode input) ≠ 0) : after output = before input := by
  have column := congrArg
    (fun vector : NormalizedVector (Qubits (encoding width).width) =>
      vector ((encoding width).encode output))
    (nativeRealizes_ket program action realized input)
  change (program.binaryMatrix environment.quantum).applyVec
    (NormalizedVector.ket ((encoding width).encode input)).vec
      ((encoding width).encode output) = _ at column
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    NormalizedVector.ket_apply] at column
  have same : (encoding width).encode output = (encoding width).encode (action input) := by
    by_contra different
    rw [if_neg different] at column
    exact nonzero column
  rw [(encoding width).encode_injective same]
  exact readout input

private lemma native_readout_diagonal {width : Nat} (program : NativeCircuit width)
    (action : Raw width → Raw width)
    (realized : UnitaryCircuit.Realizes (encoding width) program environment.quantum action)
    (before after : Raw width → Bool) (readout : ∀ state, after (action state) = before state)
    (weight : Bool → Complex) :
    ((program.binaryMatrix environment.quantum) : Matrix (Fin (2 ^ (encoding width).width))
        (Fin (2 ^ (encoding width).width)) Complex) *
        Matrix.diagonal (fun index => weight (before ((rawEquiv width).symm index))) =
      Matrix.diagonal (fun index => weight (after ((rawEquiv width).symm index))) *
        ((program.binaryMatrix environment.quantum) : Matrix (Fin (2 ^ (encoding width).width))
          (Fin (2 ^ (encoding width).width)) Complex) := by
  ext row column
  obtain ⟨input, rfl⟩ := raw_total width column
  obtain ⟨output, rfl⟩ := raw_total width row
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  change (program.binaryMatrix environment.quantum) ((encoding width).encode output) ((encoding
    width).encode input) *
      weight (before ((rawEquiv width).symm ((rawEquiv width) input))) =
    weight (after ((rawEquiv width).symm ((rawEquiv width) output))) *
      (program.binaryMatrix environment.quantum) ((encoding width).encode output) ((encoding
        width).encode input)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  by_cases zero : (program.binaryMatrix environment.quantum) ((encoding width).encode output)
      ((encoding width).encode input) = 0
  · rw [zero, zero_mul, mul_zero]
  · rw [native_readout_support program action realized before after readout input output zero]
    exact mul_comm _ _

lemma beforeDivision_diagonal {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (Q : AffinePoint E) (weight : Bool → Complex) :
    (((beforeDivision Q).binaryMatrix environment.quantum) : Matrix (Fin (2 ^ (encoding
      p.size).width))
        (Fin (2 ^ (encoding p.size).width)) Complex) * controlDiagonal p.size weight =
      controlDiagonal p.size weight *
        (((beforeDivision Q).binaryMatrix environment.quantum) : Matrix (Fin (2 ^ (encoding
          p.size).width))
          (Fin (2 ^ (encoding p.size).width)) Complex) := by
  apply native_readout_diagonal (beforeDivision Q) _ (beforeDivision_realizes Q)
    (fun state => state.1.2) (fun state => state.1.2) _ weight
  intro state
  dsimp only [Function.comp_apply]
  rw [offsetStep_control, offsetStep_control]

lemma afterMultiplication_diagonal {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (weight : Bool → Complex) :
    (((afterMultiplication E Q).binaryMatrix environment.quantum) : Matrix (Fin (2 ^ (encoding
      p.size).width))
        (Fin (2 ^ (encoding p.size).width)) Complex) * selectorDiagonal p.size weight =
      controlDiagonal p.size weight *
        (((afterMultiplication E Q).binaryMatrix environment.quantum) : Matrix (Fin (2 ^ (encoding
          p.size).width))
          (Fin (2 ^ (encoding p.size).width)) Complex) :=
  native_readout_diagonal (afterMultiplication E Q) _ (afterMultiplication_realizes E Q)
    (fun state => state.2) (fun state => state.1.2) (afterMultiplication_control_all E Q) weight

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point.Control

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
namespace Instrument

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.Execution.ContextUnion
open QuantumAlg.EllipticCurve
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

private lemma product_diagonal_commute {R : Register}
    (left right diagonal : HilbertOperator R)
    (leftLaw : left * diagonal = diagonal * left)
    (rightLaw : right * diagonal = diagonal * right) :
    (left * right) * diagonal = diagonal * (left * right) := by
  calc
    (left * right) * diagonal = left * (right * diagonal) := Matrix.mul_assoc _ _ _
    _ = left * (diagonal * right) := congrArg (fun value => left * value) rightLaw
    _ = (left * diagonal) * right := (Matrix.mul_assoc _ _ _).symm
    _ = (diagonal * left) * right := congrArg (fun value => value * right) leftLaw
    _ = diagonal * (left * right) := Matrix.mul_assoc _ _ _

private lemma pullback_diagonal_commute {R S : Register}
    (coordinates : R.Index ≃ S.Index) (operator : HilbertOperator S)
    (weight : S.Index → ℂ)
    (actual : operator * Matrix.diagonal weight = Matrix.diagonal weight * operator) :
    operator.submatrix coordinates coordinates * Matrix.diagonal (weight ∘ coordinates) =
      Matrix.diagonal (weight ∘ coordinates) * operator.submatrix coordinates coordinates := by
  rw [← Matrix.submatrix_diagonal_equiv weight coordinates,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, actual]

lemma prodTensor_reference_diagonal {R S : Register}
    (program : UnitaryOperator R) (weight : S.Index → ℂ) :
    (UnitaryOperator.prodTensor program (1 : UnitaryOperator S) :
        HilbertOperator (Register.prod R S)) * Matrix.diagonal (fun entry => weight entry.2) =
      Matrix.diagonal (fun entry => weight entry.2) *
        (UnitaryOperator.prodTensor program (1 : UnitaryOperator S) :
          HilbertOperator (Register.prod R S)) := by
  let operator : Matrix R.Index R.Index ℂ := program
  ext row column
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, UnitaryOperator.prodTensor_apply]
  change operator row.1 column.1 * (if row.2 = column.2 then (1 : ℂ) else 0) * weight column.2 =
    weight row.2 * (operator row.1 column.1 * (if row.2 = column.2 then (1 : ℂ) else 0))
  by_cases same : row.2 = column.2
  · rw [if_pos same, mul_one]
    exact (mul_comm (operator row.1 column.1) (weight column.2)).trans
      (congrArg (fun reference : S.Index => weight reference * operator row.1 column.1) same.symm)
  · rw [if_neg same, mul_zero, zero_mul, mul_zero]

lemma reset_reference_diagonal (width : Nat) (Reference : Register)
    (stored : Store (NumeratorMeasurement.context width)) (weight : Reference.Index → ℂ) :
    NumeratorResetConjugation.operator environment.quantum width Reference stored *
        Matrix.diagonal (fun entry => weight entry.2) =
      Matrix.diagonal (fun entry => weight entry.2) *
        NumeratorResetConjugation.operator environment.quantum width Reference stored := by
  unfold NumeratorResetConjugation.operator
  apply product_diagonal_commute
  · apply product_diagonal_commute
    · exact prodTensor_reference_diagonal _ weight
    · rw [ZMeasurement.projector, Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      apply congrArg Matrix.diagonal
      funext entry
      exact mul_comm _ _
  · exact prodTensor_reference_diagonal _ weight

lemma framedReset_reference_diagonal (width : Nat) (Reference : Register)
    (stored : Store (InPlaceControlled.context width)) (weight : Reference.Index → ℂ) :
    InPlaceControlled.framedResetOperator environment.quantum width Reference stored *
        Matrix.diagonal (fun entry => weight entry.2) =
      Matrix.diagonal (fun entry => weight entry.2) *
        InPlaceControlled.framedResetOperator environment.quantum width Reference stored := by
  exact pullback_diagonal_commute
    (ContextUnion.referenceBasis (NumeratorMeasurement.context width)
      (InPlaceControlled.controlContext width) (InPlaceControlled.control_disjoint width)
        Reference)
    (NumeratorResetConjugation.operator environment.quantum width
      (Register.prod (InPlaceControlled.controlContext width).register Reference)
      (InPlaceControlled.storeCoordinates width stored))
    (fun entry => weight entry.2.2)
    (reset_reference_diagonal width
      (Register.prod (InPlaceControlled.controlContext width).register Reference)
      (InPlaceControlled.storeCoordinates width stored) (fun entry => weight entry.2))

lemma controlled_reference_diagonal (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register)
    (stored : Store (InPlaceControlled.context modulus.size)) (weight : Reference.Index → ℂ) :
    InPlaceControlled.actualOperator environment.quantum operation modulus prime Reference stored *
        Matrix.diagonal (fun entry => weight entry.2) =
      Matrix.diagonal (fun entry => weight entry.2) *
        InPlaceControlled.actualOperator environment.quantum operation modulus prime Reference
          stored := by
  unfold InPlaceControlled.actualOperator
  apply product_diagonal_commute
  · apply product_diagonal_commute
    · exact prodTensor_reference_diagonal _ weight
    · exact framedReset_reference_diagonal modulus.size Reference stored weight
  · exact prodTensor_reference_diagonal _ weight

def selectorRead (width : Nat) {Reference : Register}
    (entry : (Register.prod (context width).register Reference).Index) : Fin 2 :=
  selectorBasis width
    ((ContextUnion.unionBasisEquiv (InPlaceControlled.context width) (selectorContext width)
      (selector_disjoint width) entry.1).2)

lemma arithmetic_selector_diagonal (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register) (stored : Store (context modulus.size))
    (weight : Fin 2 → ℂ) :
    arithmeticOperator (environment := environment) operation modulus prime Reference stored *
        Matrix.diagonal (fun entry => weight (selectorRead modulus.size entry)) =
      Matrix.diagonal (fun entry => weight (selectorRead modulus.size entry)) *
        arithmeticOperator (environment := environment) operation modulus prime Reference stored
          := by
  exact pullback_diagonal_commute
    (ContextUnion.referenceBasis (InPlaceControlled.context modulus.size)
      (selectorContext modulus.size) (selector_disjoint modulus.size) Reference)
    (InPlaceControlled.actualOperator environment.quantum operation modulus prime
      (Register.prod (selectorContext modulus.size).register Reference)
      (storeCoordinates modulus.size stored))
    (fun entry => weight (selectorBasis modulus.size entry.2.1))
    (controlled_reference_diagonal operation modulus prime
      (Register.prod (selectorContext modulus.size).register Reference)
      (storeCoordinates modulus.size stored)
      (fun entry => weight (selectorBasis modulus.size entry.1)))

private def controlledDiagonal (width : Nat) (Reference : Register) (weight : Fin 2 → ℂ) :
    HilbertOperator (Register.prod (InPlaceControlled.context width).register Reference) :=
  InPlaceControlled.controlBlocks width Reference (fun control => weight control • 1)

private lemma controlledDiagonal_matrix (width : Nat) (Reference : Register)
    (weight : Fin 2 → ℂ) :
    controlledDiagonal width Reference weight =
      Matrix.diagonal
        (fun entry => weight (InPlaceControlled.jointCoordinates width Reference entry).2) := by
  ext row column
  change (if (InPlaceControlled.jointCoordinates width Reference row).2 =
      (InPlaceControlled.jointCoordinates width Reference column).2 then
      weight (InPlaceControlled.jointCoordinates width Reference row).2 *
        (if (InPlaceControlled.jointCoordinates width Reference row).1 =
          (InPlaceControlled.jointCoordinates width Reference column).1 then 1 else 0) else 0) = _
  by_cases same : row = column
  · subst column
    simp
  · by_cases sector : (InPlaceControlled.jointCoordinates width Reference row).2 =
        (InPlaceControlled.jointCoordinates width Reference column).2
    · have original : (InPlaceControlled.jointCoordinates width Reference row).1 ≠
          (InPlaceControlled.jointCoordinates width Reference column).1 :=
        fun equal => same
          ((InPlaceControlled.jointCoordinates width Reference).injective (Prod.ext equal sector))
      simp [same, sector, original]
    · simp [same, sector]

lemma controlled_control_diagonal (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register)
    (stored : Store (InPlaceControlled.context modulus.size)) (weight : Fin 2 → ℂ) :
    InPlaceControlled.actualOperator environment.quantum operation modulus prime Reference stored *
        Matrix.diagonal
          (fun entry => weight (InPlaceControlled.jointCoordinates modulus.size Reference entry).2)
            =
      Matrix.diagonal
          (fun entry => weight (InPlaceControlled.jointCoordinates modulus.size Reference entry).2)
            *
        InPlaceControlled.actualOperator environment.quantum operation modulus prime Reference
          stored := by
  rw [← controlledDiagonal_matrix, InPlaceControlled.actualOperator_blocks,
    InPlaceControlled.branchOperator, controlledDiagonal,
    InPlaceControlled.controlBlocks_mul, InPlaceControlled.controlBlocks_mul]
  apply congrArg (InPlaceControlled.controlBlocks modulus.size Reference)
  funext control
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]

def controlRead (width : Nat) {Reference : Register}
    (entry : (Register.prod (context width).register Reference).Index) : Fin 2 :=
  (InPlaceControlled.jointCoordinates width
    (Register.prod (selectorContext width).register Reference)
    ((ContextUnion.referenceBasis (InPlaceControlled.context width) (selectorContext width)
      (selector_disjoint width) Reference) entry)).2

lemma arithmetic_control_diagonal (operation : InPlaceTarget.Operation) (modulus : Nat)
    (prime : Nat.Prime modulus) (Reference : Register) (stored : Store (context modulus.size))
    (weight : Fin 2 → ℂ) :
    arithmeticOperator (environment := environment) operation modulus prime Reference stored *
        Matrix.diagonal (fun entry => weight (controlRead modulus.size entry)) =
      Matrix.diagonal (fun entry => weight (controlRead modulus.size entry)) *
        arithmeticOperator (environment := environment) operation modulus prime Reference stored
          := by
  exact pullback_diagonal_commute
    (ContextUnion.referenceBasis (InPlaceControlled.context modulus.size)
      (selectorContext modulus.size) (selector_disjoint modulus.size) Reference)
    (InPlaceControlled.actualOperator environment.quantum operation modulus prime
      (Register.prod (selectorContext modulus.size).register Reference)
      (storeCoordinates modulus.size stored))
    (fun entry => weight (InPlaceControlled.jointCoordinates modulus.size
      (Register.prod (selectorContext modulus.size).register Reference) entry).2)
    (controlled_control_diagonal operation modulus prime
      (Register.prod (selectorContext modulus.size).register Reference)
      (storeCoordinates modulus.size stored) weight)

private def rawRuntime (width : Nat) (state : Raw width) : (context width).register.Index :=
  (basis width).symm ((encoding width).encode state)

private lemma rawRuntime_label (width : Nat) (state : Raw width) :
    rawRuntime width state = label width (BinaryLabelEncoding.bool.encode state.1.2)
      (BinaryLabelEncoding.bool.encode state.2)
      ((NumeratorMeasurement.frameBasis width).symm
        ((ProductPlacement.frameEncoding width).encode state.1.1)) := by
  apply (basis width).injective
  have labeled := basis_label width
    (show Fin 2 from BinaryLabelEncoding.bool.encode state.1.2)
    (show Fin 2 from BinaryLabelEncoding.bool.encode state.2)
    ((NumeratorMeasurement.frameBasis width).symm
      ((ProductPlacement.frameEncoding width).encode state.1.1))
  have frameSame := (NumeratorMeasurement.frameBasis width).apply_symm_apply
    ((ProductPlacement.frameEncoding width).encode state.1.1)
  have encoded := congrArg (fun original : Fin (2 ^ InPlaceControlled.frameWidth width) =>
    prodEquiv (m := InPlaceControlled.frameWidth width + 1) (n := 1)
      (prodEquiv (m := InPlaceControlled.frameWidth width) (n := 1)
        (original, (show Fin 2 from BinaryLabelEncoding.bool.encode state.1.2)),
          (show Fin 2 from BinaryLabelEncoding.bool.encode state.2))) frameSame
  exact ((basis width).apply_symm_apply ((encoding width).encode state)).trans
    (labeled.trans encoded).symm

private lemma controlRead_label (width : Nat) (Reference : Register)
    (control selector : Fin 2) (frame : (NumeratorMeasurement.context width).register.Index)
    (reference : Reference.Index) :
    controlRead width (label width control selector frame, reference) = control := by
  have grouped :
      ContextUnion.referenceBasis (InPlaceControlled.context width) (selectorContext width)
        (selector_disjoint width) Reference (label width control selector frame, reference) =
      (InPlaceControlled.label width control frame, ((selectorBasis width).symm selector,
        reference)) := by
    change
      (((ContextUnion.unionBasisEquiv _ _ (selector_disjoint width))
        ((ContextUnion.unionBasisEquiv _ _ (selector_disjoint width)).symm
          (InPlaceControlled.label width control frame, (selectorBasis width).symm selector))).1,
        (((ContextUnion.unionBasisEquiv _ _ (selector_disjoint width))
          ((ContextUnion.unionBasisEquiv _ _ (selector_disjoint width)).symm
            (InPlaceControlled.label width control frame,
              (selectorBasis width).symm selector))).2, reference)) = _
    rw [Equiv.apply_symm_apply]
  rw [controlRead, grouped, InPlaceControlled.jointCoordinates_label]

private lemma selectorRead_label (width : Nat) (Reference : Register)
    (control selector : Fin 2) (frame : (NumeratorMeasurement.context width).register.Index)
    (reference : Reference.Index) :
    selectorRead width (label width control selector frame, reference) = selector := by
  change selectorBasis width
    (((ContextUnion.unionBasisEquiv _ _ (selector_disjoint width))
      ((ContextUnion.unionBasisEquiv _ _ (selector_disjoint width)).symm
        (InPlaceControlled.label width control frame, (selectorBasis width).symm selector))).2) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

lemma controlRead_basis (width : Nat) (Reference : Register)
    (entry : (Register.prod (context width).register Reference).Index) :
    controlRead width entry = BinaryLabelEncoding.bool.encode
      (((Recovery.Point.Control.rawEquiv width).symm (basis width entry.1)).1.2) := by
  let state := (Recovery.Point.Control.rawEquiv width).symm (basis width entry.1)
  have actual : rawRuntime width state = entry.1 := by
    change (basis width).symm
      ((Recovery.Point.Control.rawEquiv width) ((Recovery.Point.Control.rawEquiv width).symm
        (basis width entry.1))) = entry.1
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  have transported := congrArg (fun original : (context width).register.Index =>
    controlRead width (Reference := Reference) (original, entry.2)) actual
  have labeled := congrArg (fun original : (context width).register.Index =>
    controlRead width (Reference := Reference) (original, entry.2)) (rawRuntime_label width state)
  exact transported.symm.trans (labeled.trans
    (controlRead_label width Reference
      (BinaryLabelEncoding.bool.encode state.1.2) (BinaryLabelEncoding.bool.encode state.2)
      ((NumeratorMeasurement.frameBasis width).symm
        ((ProductPlacement.frameEncoding width).encode state.1.1)) entry.2))

lemma selectorRead_basis (width : Nat) (Reference : Register)
    (entry : (Register.prod (context width).register Reference).Index) :
    selectorRead width entry = BinaryLabelEncoding.bool.encode
      (((Recovery.Point.Control.rawEquiv width).symm (basis width entry.1)).2) := by
  let state := (Recovery.Point.Control.rawEquiv width).symm (basis width entry.1)
  have actual : rawRuntime width state = entry.1 := by
    change (basis width).symm
      ((Recovery.Point.Control.rawEquiv width) ((Recovery.Point.Control.rawEquiv width).symm
        (basis width entry.1))) = entry.1
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  have transported := congrArg (fun original : (context width).register.Index =>
    selectorRead width (Reference := Reference) (original, entry.2)) actual
  have labeled := congrArg (fun original : (context width).register.Index =>
    selectorRead width (Reference := Reference) (original, entry.2)) (rawRuntime_label width state)
  exact transported.symm.trans (labeled.trans
    (selectorRead_label width Reference
      (BinaryLabelEncoding.bool.encode state.1.2) (BinaryLabelEncoding.bool.encode state.2)
      ((NumeratorMeasurement.frameBasis width).symm
        ((ProductPlacement.frameEncoding width).encode state.1.1)) entry.2))

private lemma nativeJoint_diagonal_transport (width : Nat) (Reference : Register)
    (program : NativeCircuit width)
    (before after : Fin (2 ^ (encoding width).width) → ℂ)
    (actual : ((program.binaryMatrix environment.quantum) : Matrix (Fin (2 ^ (encoding
      width).width))
        (Fin (2 ^ (encoding width).width)) ℂ) * Matrix.diagonal before =
      Matrix.diagonal after *
        ((program.binaryMatrix environment.quantum) : Matrix (Fin (2 ^ (encoding width).width))
          (Fin (2 ^ (encoding width).width)) ℂ)) :
    (MeasuredPointAddition.nativeJoint (environment := environment) width Reference program :
        HilbertOperator (Register.prod (context width).register Reference)) *
        Matrix.diagonal (fun entry => before (basis width entry.1)) =
      Matrix.diagonal (fun entry => after (basis width entry.1)) *
        (MeasuredPointAddition.nativeJoint (environment := environment) width Reference program :
          HilbertOperator (Register.prod (context width).register Reference)) := by
  ext row column
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have entry := congrArg (fun matrix : Matrix (Fin (2 ^ (encoding width).width))
    (Fin (2 ^ (encoding width).width)) ℂ => matrix (basis width row.1)
      (basis width column.1)) actual
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at entry
  change UnitaryOperator.prodTensor ((runtimeProgram width program).matrix environment.quantum)
      (1 : UnitaryOperator Reference) row column * before (basis width column.1) =
    after (basis width row.1) *
      UnitaryOperator.prodTensor ((runtimeProgram width program).matrix environment.quantum)
        (1 : UnitaryOperator Reference) row column
  rw [UnitaryOperator.prodTensor_apply, runtimeProgram_binary_matrix]
  change ((program.binaryMatrix environment.quantum) (basis width row.1) (basis width column.1) *
      (if row.2 = column.2 then (1 : ℂ) else 0)) * before (basis width column.1) =
    after (basis width row.1) *
      ((program.binaryMatrix environment.quantum) (basis width row.1) (basis width column.1) *
        (if row.2 = column.2 then (1 : ℂ) else 0))
  by_cases same : row.2 = column.2
  · simpa only [if_pos same, mul_one] using entry
  · rw [if_neg same, mul_zero, zero_mul, mul_zero]

lemma beforeDivision_physical_diagonal {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (Q : AffinePoint E) (Reference : Register) (weight : Fin 2 → ℂ) :
    (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
      (beforeDivision Q) :
        HilbertOperator (Register.prod (context p.size).register Reference)) *
        Matrix.diagonal (fun entry => weight (controlRead p.size entry)) =
      Matrix.diagonal (fun entry => weight (controlRead p.size entry)) *
        (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
          (beforeDivision Q) :
          HilbertOperator (Register.prod (context p.size).register Reference)) := by
  let operator : HilbertOperator (Register.prod (context p.size).register Reference) :=
    MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
      (beforeDivision Q)
  let rawWeight : Bool → ℂ := fun bit => weight (BinaryLabelEncoding.bool.encode bit)
  let nativeWeight := fun index : Fin (2 ^ (encoding p.size).width) =>
    rawWeight ((Recovery.Point.Control.rawEquiv p.size).symm index).1.2
  have diagonalSame :
      (Matrix.diagonal (fun entry => weight (controlRead p.size entry)) :
        HilbertOperator (Register.prod (context p.size).register Reference)) =
      Matrix.diagonal (fun entry => nativeWeight (basis p.size entry.1)) := by
    apply congrArg Matrix.diagonal
    funext entry
    exact congrArg weight (controlRead_basis p.size Reference entry)
  have actual := nativeJoint_diagonal_transport (environment := environment) p.size Reference
    (beforeDivision Q)
    nativeWeight nativeWeight (Recovery.Point.Control.beforeDivision_diagonal Q rawWeight)
  exact (congrArg (fun diagonal : HilbertOperator
      (Register.prod (context p.size).register Reference) => operator * diagonal)
    diagonalSame).trans (actual.trans
      (congrArg (fun diagonal : HilbertOperator
          (Register.prod (context p.size).register Reference) => diagonal * operator)
        diagonalSame.symm))

lemma beforeMultiplication_physical_diagonal {p : Nat} {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (Q : AffinePoint E) (Reference : Register) (weight : Fin 2 → ℂ) :
    (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
      (beforeMultiplication Q) :
        HilbertOperator (Register.prod (context p.size).register Reference)) *
        Matrix.diagonal (fun entry => weight (controlRead p.size entry)) =
      Matrix.diagonal (fun entry => weight (selectorRead p.size entry)) *
        (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
          (beforeMultiplication Q) :
          HilbertOperator (Register.prod (context p.size).register Reference)) := by
  let operator : HilbertOperator (Register.prod (context p.size).register Reference) :=
    MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
      (beforeMultiplication Q)
  let rawWeight : Bool → ℂ := fun bit => weight (BinaryLabelEncoding.bool.encode bit)
  let nativeControl := fun index : Fin (2 ^ (encoding p.size).width) =>
    rawWeight ((Recovery.Point.Control.rawEquiv p.size).symm index).1.2
  let nativeSelector := fun index : Fin (2 ^ (encoding p.size).width) =>
    rawWeight ((Recovery.Point.Control.rawEquiv p.size).symm index).2
  have controlSame :
      (Matrix.diagonal (fun entry => weight (controlRead p.size entry)) :
        HilbertOperator (Register.prod (context p.size).register Reference)) =
      Matrix.diagonal (fun entry => nativeControl (basis p.size entry.1)) := by
    apply congrArg Matrix.diagonal
    funext entry
    exact congrArg weight (controlRead_basis p.size Reference entry)
  have selectorSame :
      (Matrix.diagonal (fun entry => weight (selectorRead p.size entry)) :
        HilbertOperator (Register.prod (context p.size).register Reference)) =
      Matrix.diagonal (fun entry => nativeSelector (basis p.size entry.1)) := by
    apply congrArg Matrix.diagonal
    funext entry
    exact congrArg weight (selectorRead_basis p.size Reference entry)
  have actual := nativeJoint_diagonal_transport (environment := environment) p.size Reference
    (beforeMultiplication Q)
    nativeControl nativeSelector (Recovery.Point.Control.beforeMultiplication_diagonal Q rawWeight)
  exact (congrArg (fun diagonal : HilbertOperator
      (Register.prod (context p.size).register Reference) => operator * diagonal)
    controlSame).trans (actual.trans
      (congrArg (fun diagonal : HilbertOperator
          (Register.prod (context p.size).register Reference) => diagonal * operator)
        selectorSame.symm))

lemma afterMultiplication_physical_diagonal {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (Reference : Register) (weight : Fin 2 → ℂ) :
    (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
      (afterMultiplication E Q) :
        HilbertOperator (Register.prod (context p.size).register Reference)) *
        Matrix.diagonal (fun entry => weight (selectorRead p.size entry)) =
      Matrix.diagonal (fun entry => weight (controlRead p.size entry)) *
        (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
          (afterMultiplication E Q) :
          HilbertOperator (Register.prod (context p.size).register Reference)) := by
  let operator : HilbertOperator (Register.prod (context p.size).register Reference) :=
    MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
      (afterMultiplication E Q)
  let rawWeight : Bool → ℂ := fun bit => weight (BinaryLabelEncoding.bool.encode bit)
  let nativeControl := fun index : Fin (2 ^ (encoding p.size).width) =>
    rawWeight ((Recovery.Point.Control.rawEquiv p.size).symm index).1.2
  let nativeSelector := fun index : Fin (2 ^ (encoding p.size).width) =>
    rawWeight ((Recovery.Point.Control.rawEquiv p.size).symm index).2
  have controlSame :
      (Matrix.diagonal (fun entry => weight (controlRead p.size entry)) :
        HilbertOperator (Register.prod (context p.size).register Reference)) =
      Matrix.diagonal (fun entry => nativeControl (basis p.size entry.1)) := by
    apply congrArg Matrix.diagonal
    funext entry
    exact congrArg weight (controlRead_basis p.size Reference entry)
  have selectorSame :
      (Matrix.diagonal (fun entry => weight (selectorRead p.size entry)) :
        HilbertOperator (Register.prod (context p.size).register Reference)) =
      Matrix.diagonal (fun entry => nativeSelector (basis p.size entry.1)) := by
    apply congrArg Matrix.diagonal
    funext entry
    exact congrArg weight (selectorRead_basis p.size Reference entry)
  have actual := nativeJoint_diagonal_transport (environment := environment) p.size Reference
    (afterMultiplication E Q)
    nativeSelector nativeControl (Recovery.Point.Control.afterMultiplication_diagonal E Q rawWeight)
  exact (congrArg (fun diagonal : HilbertOperator
      (Register.prod (context p.size).register Reference) => operator * diagonal)
    selectorSame).trans (actual.trans
      (congrArg (fun diagonal : HilbertOperator
          (Register.prod (context p.size).register Reference) => diagonal * operator)
        controlSame.symm))

private lemma pair_transport {R : Register}
    (left right before middle after : HilbertOperator R)
    (first : right * before = middle * right) (second : left * middle = after * left) :
    (left * right) * before = after * (left * right) := by
  calc
    (left * right) * before = left * (right * before) := Matrix.mul_assoc _ _ _
    _ = left * (middle * right) := congrArg (fun value => left * value) first
    _ = (left * middle) * right := (Matrix.mul_assoc _ _ _).symm
    _ = (after * left) * right := congrArg (fun value => value * right) second
    _ = after * (left * right) := Matrix.mul_assoc _ _ _

lemma pointKraus_control_diagonal {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (divisionStore finalStore : Store (context p.size)) (weight : Fin 2 → ℂ) :
    pointKraus (environment := environment) E Q Reference divisionStore finalStore *
        Matrix.diagonal (fun entry => weight (controlRead p.size entry)) =
      Matrix.diagonal (fun entry => weight (controlRead p.size entry)) *
        pointKraus (environment := environment) E Q Reference divisionStore finalStore := by
  let before := (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
    (beforeDivision Q) :
    HilbertOperator (Register.prod (context p.size).register Reference))
  let divided := arithmeticOperator (environment := environment) .division p Fact.out Reference
    divisionStore
  let middle := (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
    (beforeMultiplication Q) :
    HilbertOperator (Register.prod (context p.size).register Reference))
  let multiplied := arithmeticOperator (environment := environment) .multiplication p Fact.out
    Reference finalStore
  let after := (MeasuredPointAddition.nativeJoint (environment := environment) p.size Reference
    (afterMultiplication E Q) :
    HilbertOperator (Register.prod (context p.size).register Reference))
  let dc : HilbertOperator (Register.prod (context p.size).register Reference) :=
    Matrix.diagonal (fun entry => weight (controlRead p.size entry))
  let dn : HilbertOperator (Register.prod (context p.size).register Reference) :=
    Matrix.diagonal (fun entry => weight (selectorRead p.size entry))
  have head := beforeDivision_physical_diagonal (environment := environment) Q Reference weight
  have divisionLaw := arithmetic_control_diagonal (environment := environment) .division p Fact.out
    Reference divisionStore
    weight
  have middleLaw := beforeMultiplication_physical_diagonal (environment := environment) Q Reference
    weight
  have multiplicationLaw := arithmetic_selector_diagonal (environment := environment)
    .multiplication p Fact.out Reference
    finalStore weight
  have tail := afterMultiplication_physical_diagonal (environment := environment) E Q Reference
    weight
  have first := pair_transport divided before dc dc dc head divisionLaw
  have second := pair_transport middle (divided * before) dc dc dn first middleLaw
  have third := pair_transport multiplied (middle * (divided * before)) dc dn dn second
    multiplicationLaw
  have fourth := pair_transport after (multiplied * (middle * (divided * before))) dc dn dc
    third tail
  simpa only [pointKraus, before, divided, middle, multiplied, after, dc, dn, Matrix.mul_assoc]
    using fourth

end

end Instrument
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
namespace Instrument

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.Execution.ContextUnion
open QuantumAlg.EllipticCurve
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

abbrev FiberBank (width : Nat) (Reference : Register) :=
  (NumeratorMeasurement.context width).register.Index × (Fin 2 × Reference.Index)

def fiberBasis (width : Nat) (Reference : Register) :
    (Register.prod (context width).register Reference).Index ≃
      Fin 2 × FiberBank width Reference :=
  (ContextUnion.referenceBasis (InPlaceControlled.context width) (selectorContext width)
    (selector_disjoint width) Reference).trans
    ((InPlaceControlled.jointCoordinates width
      (Register.prod (selectorContext width).register Reference)).trans
      ((Equiv.prodComm _ _).trans
        ((Equiv.refl (Fin 2)).prodCongr
          ((Equiv.refl (NumeratorMeasurement.context width).register.Index).prodCongr
            ((selectorBasis width).prodCongr (Equiv.refl Reference.Index))))))

lemma fiberBasis_control (width : Nat) (Reference : Register)
    (entry : (Register.prod (context width).register Reference).Index) :
    (fiberBasis width Reference entry).1 = controlRead width entry := rfl

lemma fiberBasis_symm (width : Nat) (Reference : Register)
    (bit : Fin 2) (bank : FiberBank width Reference) :
    (fiberBasis width Reference).symm (bit, bank) =
      (label width bit bank.2.1 bank.1, bank.2.2) := rfl

lemma pointKraus_off_fiber {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (divisionStore finalStore : Store (context p.size))
    (row column : (Register.prod (context p.size).register Reference).Index)
    (different : controlRead p.size row ≠ controlRead p.size column) :
    pointKraus (environment := environment) E Q Reference divisionStore finalStore row column = 0
      := by
  have entry := congrArg
    (fun matrix : Matrix (Register.prod (context p.size).register Reference).Index
        (Register.prod (context p.size).register Reference).Index Complex => matrix row column)
    (pointKraus_control_diagonal (environment := environment) E Q Reference divisionStore finalStore
      (fun bit => if bit = controlRead p.size column then 1 else 0))
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, if_neg different,
    ite_true, mul_one, zero_mul] at entry
  exact entry

def pointBankBlock {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (divisionStore finalStore : Store (context p.size)) (bit : Fin 2) :
    Matrix (FiberBank p.size Reference) (FiberBank p.size Reference) Complex :=
  (pointKraus (environment := environment) E Q Reference divisionStore finalStore).submatrix
    (fun bank => (fiberBasis p.size Reference).symm (bit, bank))
    (fun bank => (fiberBasis p.size Reference).symm (bit, bank))

lemma pointKraus_fiber_entry {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Reference : Register)
    (divisionStore finalStore : Store (context p.size))
    (rowBit columnBit : Fin 2) (rowBank columnBank : FiberBank p.size Reference) :
    pointKraus (environment := environment) E Q Reference divisionStore finalStore
        ((fiberBasis p.size Reference).symm (rowBit, rowBank))
        ((fiberBasis p.size Reference).symm (columnBit, columnBank)) =
      if rowBit = columnBit then
        pointBankBlock (environment := environment) E Q Reference divisionStore finalStore rowBit
          rowBank columnBank
      else 0 := by
  by_cases same : rowBit = columnBit
  · subst columnBit
    rw [if_pos rfl]
    rfl
  · rw [if_neg same]
    apply pointKraus_off_fiber
    intro equal
    apply same
    simpa only [← fiberBasis_control, Equiv.apply_symm_apply] using equal

end

end Instrument
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
namespace Instrument

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.Execution.ContextUnion
open QuantumAlg.EllipticCurve
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.MeasuredPointAddition
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

lemma pointKraus_memory_entry {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (Q : AffinePoint E) (Memory Reference : Register)
    (divisionStore finalStore : Store (context p.size))
    (row column : (context p.size).register.Index)
    (rowMemory columnMemory : Memory.Index) (rowReference columnReference : Reference.Index) :
    pointKraus (environment := environment) E Q (Register.prod Memory Reference) divisionStore
      finalStore
        (row, (rowMemory, rowReference)) (column, (columnMemory, columnReference)) =
      pointKraus (environment := environment) E Q Reference divisionStore finalStore
        (row, rowReference) (column, columnReference) *
          (if rowMemory = columnMemory then (1 : Complex) else 0) := by
  obtain ⟨localKernel, factor⟩ := pointKraus_reference_factor (environment := environment) E Q
    divisionStore finalStore
  rw [factor (Register.prod Memory Reference), factor Reference]
  change localKernel row column *
      (if (rowMemory, rowReference) = (columnMemory, columnReference) then (1 : Complex) else 0) =
    (localKernel row column * (if rowReference = columnReference then (1 : Complex) else 0)) *
      (if rowMemory = columnMemory then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

end

end Instrument
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
