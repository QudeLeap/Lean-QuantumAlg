/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.Circuit.ClassicalTag.Encoding
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Instrument.Stored

/-!
# Point body with complete stored history fibers

The point continuation uses the native fixed-context tag law, retaining every
stored history fiber.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open scoped Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- A tensor identity selects the same reference entries in an arbitrary matrix sandwich. -/
private lemma tensor_conjugation_entry {Local Reference : Type}
    [Fintype Local] [Fintype Reference]
    (operator : Matrix Local Local ℂ)
    (density : Matrix (Local × Reference) (Local × Reference) ℂ)
    (left right : Local) (leftRef rightRef : Reference) :
    ((operator ⊗ₖ (1 : Matrix Reference Reference ℂ)) * density *
      (operator ⊗ₖ (1 : Matrix Reference Reference ℂ)).conjTranspose)
        (left, leftRef) (right, rightRef) =
      (operator * density.submatrix (fun index => (index, leftRef))
        (fun index => (index, rightRef)) * operator.conjTranspose) left right := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  change (∑ second : Local × Reference,
    (∑ first : Local × Reference,
      (operator left first.1 * (1 : Matrix Reference Reference ℂ) leftRef first.2) *
        density first second) *
      star (operator right second.1 * (1 : Matrix Reference Reference ℂ) rightRef second.2)) = _
  simp [Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

/-- The existing five-factor reference identity commutes with fixing one complete old tag. -/
private lemma pointKraus_tag_conjugation {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (Tag Reference : Register)
    (divisionStore finalStore : Store (MeasuredPointAddition.context p.size))
    (density : Matrix
      ((MeasuredPointAddition.context p.size).register.prod (Tag.prod Reference)).Index
      ((MeasuredPointAddition.context p.size).register.prod (Tag.prod Reference)).Index ℂ)
    (tag : Tag.Index) :
    (Recovery.Point.Instrument.pointKraus (environment := environment) E Q (Tag.prod Reference)
      divisionStore finalStore *
      density *
      (Recovery.Point.Instrument.pointKraus (environment := environment) E Q (Tag.prod Reference)
        divisionStore finalStore).conjTranspose).submatrix
          (fun index : ((MeasuredPointAddition.context p.size).register.prod Reference).Index =>
            (index.1, (tag, index.2)))
          (fun index : ((MeasuredPointAddition.context p.size).register.prod Reference).Index =>
            (index.1, (tag, index.2))) =
      Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
        divisionStore finalStore *
        density.submatrix
          (fun index : ((MeasuredPointAddition.context p.size).register.prod Reference).Index =>
            (index.1, (tag, index.2)))
          (fun index : ((MeasuredPointAddition.context p.size).register.prod Reference).Index =>
            (index.1, (tag, index.2))) *
        (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
          divisionStore
          finalStore).conjTranspose := by
  obtain ⟨localKernel, factor⟩ :=
    Recovery.Point.Instrument.pointKraus_reference_factor (environment := environment) E Q
      divisionStore finalStore
  ext row column
  rw [factor (Tag.prod Reference), factor Reference]
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  change (∑ second :
      (MeasuredPointAddition.context p.size).register.Index × (Tag.Index × Reference.Index),
    (∑ first :
        (MeasuredPointAddition.context p.size).register.Index × (Tag.Index × Reference.Index),
      (localKernel row.1 first.1 *
        (1 : HilbertOperator (Tag.prod Reference)) (tag, row.2) first.2) *
        density first second) *
      star (localKernel column.1 second.1 *
        (1 : HilbertOperator (Tag.prod Reference)) (tag, column.2) second.2)) =
    ∑ second : (MeasuredPointAddition.context p.size).register.Index × Reference.Index,
      (∑ first : (MeasuredPointAddition.context p.size).register.Index × Reference.Index,
        (localKernel row.1 first.1 *
          (1 : HilbertOperator Reference) row.2 first.2) *
          density (first.1, (tag, first.2)) (second.1, (tag, second.2))) *
        star (localKernel column.1 second.1 *
          (1 : HilbertOperator Reference) column.2 second.2)
  simp [Fintype.sum_prod_type, Matrix.one_apply, apply_ite]

/-- Encoding retains each original old-cell fiber as the entire diagonal tag matrix block. -/
private lemma encodeOracleTag_fiber_matrix {ctx : RuntimeCtx .quantum}
    {Reference Tag : Register} {Hidden History : Type}
    [Fintype Hidden] [Fintype History]
    (state : State ctx Reference (Hidden × (History × Tag.Index))) (tag : Tag.Index) :
    (State.encodeOracleTag (Tag := Tag) state).quantumMarginal.matrix.submatrix
        (fun index : (ctx.register.prod Reference).Index =>
          (index.1, (tag, index.2)))
        (fun index : (ctx.register.prod Reference).Index =>
          (index.1, (tag, index.2))) =
      (state.filterClassical (fun record => record.2.2.2 = tag)).quantumMarginal.matrix := by
  ext row column
  simp only [Matrix.submatrix_apply, ExecutionState.quantumMarginal, Matrix.sum_apply,
    Fintype.sum_prod_type, State.encodeOracleTag_entry, if_true,
    ExecutionState.filterClassical_block, apply_ite, DensityOperator.zero_matrix]
  apply Finset.sum_congr rfl
  intro store _
  apply Finset.sum_congr rfl
  intro hidden _
  apply Finset.sum_congr rfl
  intro history _
  simp only [Matrix.ite_apply]
  exact (Fintype.sum_ite_eq' tag (fun original : Tag.Index =>
    (state.block (store, (hidden, (history, original)))).matrix row column)).symm

/-- Decoding fixes the old tag and final complete Store before any history sum is taken. -/
private lemma decodeExecutionTag_store_fiber_matrix {ctx : RuntimeCtx .quantum}
    {Reference Tag : Register} {Hidden History Path : Type}
    [Fintype Hidden] [Fintype History] [Fintype Path]
    (state : State ctx (Tag.prod Reference) (Hidden × (History × Path)))
    (stored : Store ctx) (tag : Tag.Index) :
    ((State.decodeExecutionTag (Tag := Tag) state).filterClassical
      (fun record => record.1 = stored ∧ record.2.2.1.2 = tag)).quantumMarginal.matrix =
      (state.filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix.submatrix
        (fun index : (ctx.register.prod Reference).Index =>
          (index.1, (tag, index.2)))
        (fun index : (ctx.register.prod Reference).Index =>
          (index.1, (tag, index.2))) := by
  ext row column
  simp only [Matrix.submatrix_apply, ExecutionState.quantumMarginal, Matrix.sum_apply,
    ExecutionState.filterClassical_block, apply_ite, DensityOperator.zero_matrix,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro originalStore _
  apply Finset.sum_congr rfl
  intro hidden _
  apply Finset.sum_congr rfl
  intro history _
  by_cases sameStore : originalStore = stored
  · simp only [sameStore, true_and, if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro path _
    simp only [Matrix.ite_apply, State.decodeExecutionTag_entry, Matrix.zero_apply]
    simpa only [sameStore] using Fintype.sum_ite_eq' tag (fun original : Tag.Index =>
      (state.block (originalStore, (hidden, (history, path)))).matrix
        (row.1, (original, row.2)) (column.1, (original, column.2)))
  · simp only [sameStore, false_and, if_false]
    change (∑ _ : Tag.Index, ∑ _ : Path, (0 : ℂ)) = ∑ _ : Path, (0 : ℂ)
    simp only [Finset.sum_const_zero]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Fix the original complete Store and old tag before summing only actual internal paths. -/
lemma oldPointBody_store_retained_fiber {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) {Reference Tag : Register}
    {History : Type} [Fintype History]
    (state : State (MeasuredPointAddition.context p.size) Reference
      (ClassicalOracleModel.empty.HiddenState × (History × Tag.Index)))
    (finalStore : Store (MeasuredPointAddition.context p.size)) (tag : Tag.Index)
    (allowAllocation : Bool := true) :
    (((MeasuredPointAddition.body E Q allowAllocation).execute environment Reference
      state).filterClassical
      (fun record => record.1 = finalStore ∧ record.2.2.1.2 = tag)).quantumMarginal.matrix =
      ∑ divisionStore : Store (MeasuredPointAddition.context p.size),
        Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
          divisionStore finalStore *
          (state.filterClassical (fun record => record.2.2.2 = tag)).quantumMarginal.matrix *
          (Recovery.Point.Instrument.pointKraus (environment := environment) E Q Reference
            divisionStore
            finalStore).conjTranspose := by
  change (((MeasuredPointAddition.body E Q false).execute environment Reference
    state).filterClassical
    (fun record => record.1 = finalStore ∧ record.2.2.1.2 = tag)).quantumMarginal.matrix = _
  rw [Circuit.execute_encodedClassicalTag (environment := environment)
    (MeasuredPointAddition.body E Q false) state,
    decodeExecutionTag_store_fiber_matrix,
    Recovery.Point.Instrument.body_store_matrix E Q (Reference := Tag.prod Reference)
      (State.encodeOracleTag state) finalStore false]
  ext row column
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro divisionStore _
  have fixedTag := pointKraus_tag_conjugation (environment := environment) E Q Tag Reference
    divisionStore finalStore
    (State.encodeOracleTag (Tag := Tag) state).quantumMarginal.matrix tag
  rw [encodeOracleTag_fiber_matrix (Tag := Tag)] at fixedTag
  exact congrArg (fun matrix => matrix row column) fixedTag

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Point
