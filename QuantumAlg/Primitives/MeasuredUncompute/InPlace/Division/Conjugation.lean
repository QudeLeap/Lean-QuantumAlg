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

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual placed native matrix acts beside the unchanged complete external reference. -/
def native (interpretation : OracleModel.empty.Interpretation) (width : Nat) (Reference : Register)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width)) :
    UnitaryOperator (Register.prod (context width).register Reference) :=
  UnitaryOperator.prodTensor ((NumeratorRuntime.program width body).matrix interpretation)
    (1 : UnitaryOperator Reference)

private lemma fixed_density (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    (ExecutionState.filterClassical
      ((NumeratorRuntime.code width body).execute environment Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      DensityOperator.applyUnitary (native environment.quantum width Reference body)
        (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal :=
  Circuit.unitary_store_filter (NumeratorRuntime.program width body) environment
    state (fun original => original = stored)

private lemma selected_density (width : Nat)
    (body : CShape.Value (.fixedVector width (.finite 2)) →
      UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    (ExecutionState.filterClassical
      ((NumeratorRuntime.selected width body).execute environment Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      DensityOperator.applyUnitary (native environment.quantum width Reference (body
        (stored.read (input width))))
        (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal := by
  apply DensityOperator.ext
  exact Circuit.selectedUnitary_store_matrix (input width)
    (fun value => NumeratorRuntime.program width (body value)) environment state stored

private lemma native_source (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty (InverseRuntimeFrame.source width))
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (stored : Store (context width)) :
    NumeratorStoredProjection.source width
      ((NumeratorRuntime.code width body).execute environment Reference state) stored =
      DensityOperator.applyUnitary (native environment.quantum width Reference body)
        (NumeratorStoredProjection.source width state stored) :=
  Circuit.unitary_store_filter (NumeratorRuntime.program width body) environment
    state
    (fun original => Circuit.writeMeasurementPath (gates := AlgorithmGate.model)
      (oracles := .empty) (operations := .empty) (classicalOracles := .empty)
      (readouts width) original
      (Circuit.measurementBasisPath (gates := AlgorithmGate.model) (oracles := .empty)
        (operations := .empty) (classicalOracles := .empty) (readouts width)
        (NumeratorStoredProjection.representative width
          (NumeratorReset.outcome (stored.read (input width))))) = stored)

/-- Matrix product of precisely the six real body blocks for the real stored outcomes. -/
def operator (interpretation : OracleModel.empty.Interpretation) (modulus : Nat) (prime :
  Nat.Prime modulus) (Reference : Register)
    (stored : Store (context modulus.size)) :
    HilbertOperator (Register.prod (context modulus.size).register Reference) :=
  (native interpretation modulus.size Reference (FrameSwap.program modulus.size) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    (native interpretation modulus.size Reference
      (NumeratorCorrection.member modulus.size (InPlaceArithmetic.modulusWord modulus)
        (stored.read (input modulus.size))) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    (native interpretation modulus.size Reference (NativeEEAFrame.backward modulus prime) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    NumeratorResetConjugation.operator interpretation modulus.size Reference stored *
    (native interpretation modulus.size Reference
      (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus)) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    (native interpretation modulus.size Reference (NativeEEAFrame.forward modulus prime) :
      HilbertOperator (Register.prod (context modulus.size).register Reference))

/-- Every complete stored-reference block belongs to this same actual circuit execution. -/
lemma body_matrix (modulus : Nat) (prime : Nat.Prime modulus)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context modulus.size) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (context modulus.size)) :
    (ExecutionState.filterClassical
      ((InPlaceDivision.body modulus prime).execute environment Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      operator environment.quantum modulus prime Reference stored *
        (NumeratorStoredProjection.source modulus.size state stored).matrix *
        (operator environment.quantum modulus prime Reference stored).conjTranspose := by
  let tail4 := Circuit.seq
    (NumeratorCorrection.code modulus.size (InPlaceArithmetic.modulusWord modulus))
    (InPlaceDivision.swap modulus.size)
  let tail3 := Circuit.seq (InPlaceDivision.backward modulus prime) tail4
  let tail2 := Circuit.seq (NumeratorReset.code modulus.size) tail3
  let tail1 := Circuit.seq (InPlaceDivision.product modulus) tail2
  let state1 := (InPlaceDivision.forward modulus prime).execute environment Reference state
  let state2 := (InPlaceDivision.product modulus).execute environment Reference state1
  let state3 := (NumeratorReset.code modulus.size).execute environment Reference state2
  let state4 := (InPlaceDivision.backward modulus prime).execute environment Reference state3
  change (ExecutionState.filterClassical
    ((Circuit.seq (InPlaceDivision.forward modulus prime) tail1).execute environment Reference
      state)
    (fun entry => entry.1 = stored)).quantumMarginal.matrix = _
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (InPlaceDivision.forward modulus prime)
      tail1 environment state stored)).trans ?_
  change (ExecutionState.filterClassical
    ((Circuit.seq (InPlaceDivision.product modulus) tail2).execute environment Reference state1)
    (fun entry => entry.1 = stored)).quantumMarginal.matrix = _
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (InPlaceDivision.product modulus) tail2 environment state1
      stored)).trans ?_
  change (ExecutionState.filterClassical
    ((Circuit.seq (NumeratorReset.code modulus.size) tail3).execute environment Reference state2)
    (fun entry => entry.1 = stored)).quantumMarginal.matrix = _
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (NumeratorReset.code modulus.size) tail3 environment state2
      stored)).trans ?_
  change (ExecutionState.filterClassical
    ((Circuit.seq (InPlaceDivision.backward modulus prime) tail4).execute environment Reference
      state3)
    (fun entry => entry.1 = stored)).quantumMarginal.matrix = _
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (InPlaceDivision.backward modulus prime)
      tail4 environment state3 stored)).trans ?_
  change (ExecutionState.filterClassical
    ((Circuit.seq (NumeratorCorrection.code modulus.size
      (InPlaceArithmetic.modulusWord modulus)) (InPlaceDivision.swap modulus.size)).execute
        environment Reference state4) (fun entry => entry.1 = stored)).quantumMarginal.matrix =
        _
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (NumeratorCorrection.code modulus.size
      (InPlaceArithmetic.modulusWord modulus)) (InPlaceDivision.swap modulus.size) environment
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
