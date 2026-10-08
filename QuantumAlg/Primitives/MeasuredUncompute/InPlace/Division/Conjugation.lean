/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Division
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset.Conjugation

/-!
# Complete stored blocks of the actual in-place division body

The same execution performs both EEA passes, the product, H/Z/stored-X,
the stored phase correction and the final swap. Its complete final-store
block is a conjugation by those exact native matrices in that exact order.
The original classical fibers come only from the actual measurement write
function; every external-reference entry is retained
[LYL+26, sec_point_add/sec_point_add.tex:45-105].
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceDivisionConjugation

noncomputable section

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual placed native matrix acts beside the unchanged complete external reference. -/
def native (width : Nat) (Reference : Register)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width)) :
    UnitaryOperator (Register.prod (context width).register Reference) :=
  UnitaryOperator.prodTensor (NumeratorRuntime.program width body).matrix
    (1 : UnitaryOperator Reference)

private theorem fixed_density (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    (ExecutionState.filterClassical
      ((NumeratorRuntime.code width body).execute Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      DensityOperator.applyUnitary (native width Reference body)
        (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal :=
  Circuit.unitary_store_filter (NumeratorRuntime.program width body)
    state (fun original => original = stored)

private theorem selected_density (width : Nat)
    (body : CShape.Value (.fixedVector width (.finite 2)) →
      UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    (ExecutionState.filterClassical
      ((NumeratorRuntime.selected width body).execute Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      DensityOperator.applyUnitary (native width Reference (body (stored.read (input width))))
        (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal := by
  apply DensityOperator.ext
  exact Circuit.selectedUnitary_store_matrix (input width)
    (fun value => NumeratorRuntime.program width (body value)) state stored

private theorem native_source (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    NumeratorStoredProjection.source width
      ((NumeratorRuntime.code width body).execute Reference state) stored =
      DensityOperator.applyUnitary (native width Reference body)
        (NumeratorStoredProjection.source width state stored) :=
  Circuit.unitary_store_filter (NumeratorRuntime.program width body)
    state
    (fun original => Circuit.writeMeasurementPath (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts width) original
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := .empty) (classicalOracles := .empty) (readouts width)
        (NumeratorStoredProjection.representative width
          (NumeratorReset.outcome (stored.read (input width))))) = stored)

/-- Matrix product of precisely the six real body blocks for the real stored outcomes. -/
def operator (modulus : Nat) (prime : Nat.Prime modulus) (Reference : Register)
    (stored : Store (context modulus.size)) :
    HilbertOperator (Register.prod (context modulus.size).register Reference) :=
  (native modulus.size Reference (FrameSwap.program modulus.size) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    (native modulus.size Reference
      (NumeratorCorrection.member modulus.size (InPlaceArithmetic.modulusWord modulus)
        (stored.read (input modulus.size))) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    (native modulus.size Reference (NativeEEAFrame.backward modulus prime) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    NumeratorResetConjugation.operator modulus.size Reference stored *
    (native modulus.size Reference
      (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus)) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    (native modulus.size Reference (NativeEEAFrame.forward modulus prime) :
      HilbertOperator (Register.prod (context modulus.size).register Reference))

/-- Every complete stored-reference block belongs to this same actual circuit execution. -/
theorem body_matrix (modulus : Nat) (prime : Nat.Prime modulus)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (context modulus.size)) :
    (ExecutionState.filterClassical
      ((InPlaceDivision.body modulus prime).execute Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      operator modulus prime Reference stored *
        (NumeratorStoredProjection.source modulus.size state stored).matrix *
        (operator modulus prime Reference stored).conjTranspose := by
  let tail4 := Circuit.seq
    (NumeratorCorrection.code modulus.size (InPlaceArithmetic.modulusWord modulus))
    (InPlaceDivision.swap modulus.size)
  let tail3 := Circuit.seq (InPlaceDivision.backward modulus prime) tail4
  let tail2 := Circuit.seq (NumeratorReset.code modulus.size) tail3
  let tail1 := Circuit.seq (InPlaceDivision.product modulus) tail2
  let state1 := (InPlaceDivision.forward modulus prime).execute Reference state
  let state2 := (InPlaceDivision.product modulus).execute Reference state1
  let state3 := (NumeratorReset.code modulus.size).execute Reference state2
  let state4 := (InPlaceDivision.backward modulus prime).execute Reference state3
  change (ExecutionState.filterClassical
    ((Circuit.seq (InPlaceDivision.forward modulus prime) tail1).execute Reference state)
    (fun entry => entry.1 = stored)).quantumMarginal.matrix = _
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (InPlaceDivision.forward modulus prime)
      tail1 state stored)).trans ?_
  change (ExecutionState.filterClassical
    ((Circuit.seq (InPlaceDivision.product modulus) tail2).execute Reference state1)
    (fun entry => entry.1 = stored)).quantumMarginal.matrix = _
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (InPlaceDivision.product modulus) tail2 state1 stored)).trans ?_
  change (ExecutionState.filterClassical
    ((Circuit.seq (NumeratorReset.code modulus.size) tail3).execute Reference state2)
    (fun entry => entry.1 = stored)).quantumMarginal.matrix = _
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (NumeratorReset.code modulus.size) tail3 state2 stored)).trans ?_
  change (ExecutionState.filterClassical
    ((Circuit.seq (InPlaceDivision.backward modulus prime) tail4).execute Reference state3)
    (fun entry => entry.1 = stored)).quantumMarginal.matrix = _
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (InPlaceDivision.backward modulus prime)
      tail4 state3 stored)).trans ?_
  change (ExecutionState.filterClassical
    ((Circuit.seq (NumeratorCorrection.code modulus.size
      (InPlaceArithmetic.modulusWord modulus)) (InPlaceDivision.swap modulus.size)).execute
        Reference state4) (fun entry => entry.1 = stored)).quantumMarginal.matrix = _
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (NumeratorCorrection.code modulus.size
      (InPlaceArithmetic.modulusWord modulus)) (InPlaceDivision.swap modulus.size)
      state4 stored)).trans ?_
  refine (congrArg DensityOperator.matrix
    (fixed_density modulus.size (FrameSwap.program modulus.size) _ stored)).trans ?_
  unfold NumeratorCorrection.code
  erw [selected_density]
  unfold InPlaceDivision.backward
  erw [fixed_density]
  erw [NumeratorResetConjugation.actual_density]
  unfold InPlaceDivision.product
  erw [native_source]
  unfold InPlaceDivision.forward
  erw [native_source]
  simp only [DensityOperator.applyUnitary_matrix, ZMeasurement.branch,
    operator, native, NumeratorResetConjugation.operator,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end QuantumAlg.MeasuredUncompute.InPlaceDivisionConjugation
