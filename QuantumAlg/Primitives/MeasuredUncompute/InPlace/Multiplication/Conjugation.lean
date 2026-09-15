/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Multiplication
import all QuantumAlg.Primitives.MeasuredUncompute.Numerator.Reset.Conjugation

/-!
# Complete stored blocks of the actual in-place multiplication body

The same execution performs the native product, H/Z/stored-X reset,
reused EEA forward, stored phase correction, the identical reused EEA
backward and the actual final swap. Its final-store block is conjugated
by precisely those real matrices in precisely that order. Original
classical fibers come only from the actual measurement writes, and every
external-reference matrix entry is retained
[LYL+26, sec_point_add/sec_point_add.tex:32-36,119-122].

The reusable native and store-filter identities below are local proof
steps for this one actual Circuit. They introduce neither another
measurement semantics nor another arithmetic program or resource ledger.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceMultiplicationConjugation

noncomputable section

open Execution MAU.Inversion.SharedEEA NumeratorMeasurement

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- The actual placed native matrix acts beside the unchanged complete external reference. -/
private def native (width : Nat) (Reference : Register)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width)) :
    UnitaryOperator (Register.prod (context width).register Reference) :=
  UnitaryOperator.prodTensor (NumeratorRuntime.program width body).matrix
    (1 : UnitaryOperator Reference)

private theorem fixed_density (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (within : body.physical_idx ⊆ List.range (OutputCopy.encoding width).width)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference History) (stored : Store (context width)) :
    (ExecutionState.filterClassical
      ((NumeratorRuntime.code width body within).execute Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      DensityOperator.applyUnitary (native width Reference body)
        (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal :=
  Circuit.unitary_store_filter (NumeratorRuntime.program width body)
    (NumeratorRuntime.program_physical width body within) state (fun original => original = stored)

private theorem selected_density (width : Nat)
    (body : CShape.Value (.fixedVector width (.finite 2)) →
      UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (within : ∀ value, (body value).physical_idx ⊆ List.range (OutputCopy.encoding width).width)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference History) (stored : Store (context width)) :
    (ExecutionState.filterClassical
      ((NumeratorRuntime.selected width body within).execute Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal =
      DensityOperator.applyUnitary (native width Reference (body (stored.read (input width))))
        (state.filterClassical (fun entry => entry.1 = stored)).quantumMarginal := by
  apply DensityOperator.ext
  exact Circuit.selectedUnitary_store_matrix (input width)
    (fun value => NumeratorRuntime.program width (body value))
    (fun value => NumeratorRuntime.program_physical width (body value) (within value)) state stored

private theorem native_source (width : Nat)
    (body : UnitaryCircuit (Qubits (OutputCopy.encoding width).width))
    (within : body.physical_idx ⊆ List.range (OutputCopy.encoding width).width)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context width) Reference History) (stored : Store (context width)) :
    NumeratorStoredProjection.source width
      ((NumeratorRuntime.code width body within).execute Reference state) stored =
      DensityOperator.applyUnitary (native width Reference body)
        (NumeratorStoredProjection.source width state stored) :=
  Circuit.unitary_store_filter (NumeratorRuntime.program width body)
    (NumeratorRuntime.program_physical width body within) state
    (fun original => Circuit.writeMeasurementPath (readouts width) original
      (Circuit.measurementBasisPath (readouts width)
        (NumeratorStoredProjection.representative width
          (NumeratorReset.outcome (stored.read (input width))))) = stored)

/-- Matrix product of precisely the six multiplication blocks for the actually stored outcomes. -/
def operator (modulus : Nat) (prime : Nat.Prime modulus) (Reference : Register)
    (stored : Store (context modulus.size)) :
    HilbertOperator (Register.prod (context modulus.size).register Reference) :=
  (native modulus.size Reference (FrameSwap.program modulus.size) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    (native modulus.size Reference (NativeEEAFrame.backward modulus prime) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    (native modulus.size Reference
      (NumeratorCorrection.member modulus.size (InPlaceArithmetic.modulusWord modulus)
        (stored.read (input modulus.size))) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    (native modulus.size Reference (NativeReusedEEA.forward modulus prime) :
      HilbertOperator (Register.prod (context modulus.size).register Reference)) *
    NumeratorResetConjugation.operator modulus.size Reference stored *
    (native modulus.size Reference
      (NativeProductFrame.program modulus.size (InPlaceArithmetic.modulusWord modulus)) :
      HilbertOperator (Register.prod (context modulus.size).register Reference))

/-- Every complete stored-reference block belongs to this same actual circuit execution. -/
theorem body_matrix (modulus : Nat) (prime : Nat.Prime modulus)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (context modulus.size) Reference History)
    (stored : Store (context modulus.size)) :
    (ExecutionState.filterClassical
      ((InPlaceMultiplication.body modulus prime).execute Reference state)
      (fun entry => entry.1 = stored)).quantumMarginal.matrix =
      operator modulus prime Reference stored *
        (NumeratorStoredProjection.source modulus.size state stored).matrix *
        (operator modulus prime Reference stored).conjTranspose := by
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal _ _ state stored)).trans ?_
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal _ _ _ stored)).trans ?_
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal _ _ _ stored)).trans ?_
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal _ _ _ stored)).trans ?_
  refine (congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal _ _ _ stored)).trans ?_
  refine (congrArg DensityOperator.matrix
    (fixed_density modulus.size (FrameSwap.program modulus.size) _ _ stored)).trans ?_
  unfold InPlaceMultiplication.backward
  erw [fixed_density]
  unfold NumeratorCorrection.code
  rw [selected_density]
  unfold InPlaceMultiplication.forward
  erw [fixed_density]
  erw [NumeratorResetConjugation.actual_density]
  unfold InPlaceMultiplication.product
  erw [native_source]
  simp only [DensityOperator.applyUnitary_matrix, ZMeasurement.branch,
    operator, native, NumeratorResetConjugation.operator,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

end

end QuantumAlg.MeasuredUncompute.InPlaceMultiplicationConjugation
