/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Instrument.Stored
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Fiber.Retained
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Path.Density
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.History.Matrices
import all QuantumAlg.Core.Execution.Circuit.ClassicalTag.Encoding
import all QuantumAlg.Core.Execution.Circuit.History

/-!
# Actual stage and legal-path matrices at every original history predicate

The complete original stage law is lifted through an explicit mathematical
reference tag, retaining every full Store and external Reference entry. The
tag represents an existing history predicate; it is not a physical operation.
The actual sequential Path reassociation then carries that same predicate
through the original finite legal-path CP sum, including every zero term.

This owner adds no caller-state certificate, clean Store premise, probability pruning,
normalization or common output sigma. It does not compare the old and new fine generated
histories or prove their complete instruments.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.HistoryPaths

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open ScalarMultiplication.MeasuredPlacement
open Recovery.Stage
open Recovery.Stage.PointCoordinates.StageWord.PathWord
open Recovery.Stage.PointCoordinates.StageWord.StoredRecursion
open scoped BigOperators Kronecker

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- The same intersection identity accepts the actual callers' proposition decisions. -/
private lemma filter_intersection_decisions {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (first second : C → Prop)
    {firstDecision : DecidablePred first} {secondDecision : DecidablePred second}
    {combinedDecision : DecidablePred (fun record => second record ∧ first record)} :
    @ExecutionState.filterClassical C _ R
        (@ExecutionState.filterClassical C _ R state first firstDecision) second secondDecision =
      @ExecutionState.filterClassical C _ R state
        (fun record => second record ∧ first record) combinedDecision := by
  apply ExecutionState.ext
  intro record
  by_cases keepFirst : first record <;> by_cases keepSecond : second record <;>
    simp only [ExecutionState.filterClassical_block, keepFirst, keepSecond,
      true_and, false_and, and_false, if_true, if_false]

/-- Nested full classical filters intersect without changing any quantum/reference block. -/
private lemma filter_intersection {C : Type} [Fintype C] {R : Register}
    (state : ExecutionState C R) (first second : C → Prop) :
    (state.filterClassical first).filterClassical second =
      state.filterClassical (fun record => second record ∧ first record) := by
  apply ExecutionState.ext
  intro record
  by_cases keepFirst : first record <;> by_cases keepSecond : second record <;>
    simp only [ExecutionState.filterClassical_block, keepFirst, keepSecond,
      true_and, false_and, and_false, if_true, if_false]

/-- A real placement changes local coordinates while keeping the complete reference factor. -/
private lemma embedded_tensor_identity {child caller : RuntimeCtx .quantum}
    (placement : ContextEmbedding child caller) (operator : HilbertOperator child.register)
    (Reference : Register) :
    (operator ⊗ₖ (1 : HilbertOperator (placement.frame.register.prod Reference))).submatrix
        (placement.referenceBasis Reference) (placement.referenceBasis Reference) =
      ((operator ⊗ₖ (1 : HilbertOperator placement.frame.register)).submatrix
        placement.basis placement.basis) ⊗ₖ (1 : HilbertOperator Reference) := by
  ext row column
  let rowLocal := placement.basis row.1
  let columnLocal := placement.basis column.1
  change operator rowLocal.1 columnLocal.1 *
      (if (rowLocal.2, row.2) = (columnLocal.2, column.2) then (1 : ℂ) else 0) =
    (operator rowLocal.1 columnLocal.1 *
      (if rowLocal.2 = columnLocal.2 then (1 : ℂ) else 0)) *
      (if row.2 = column.2 then 1 else 0)
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

/-- Multiplication keeps the same literal identity on the complete external Reference. -/
private lemma tensor_identity_mul {Local Reference : Register}
    (first second : HilbertOperator Local) :
    (first ⊗ₖ (1 : HilbertOperator Reference)) *
        (second ⊗ₖ (1 : HilbertOperator Reference)) =
      (first * second) ⊗ₖ (1 : HilbertOperator Reference) := by
  simpa only [Matrix.one_mul] using
    (Matrix.mul_kronecker_mul first second
      (1 : HilbertOperator Reference) (1 : HilbertOperator Reference)).symm

/-- The original point matrix has one dirty-bank operator beside every unchanged Reference. -/
lemma pointMatrix_reference_factor {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (Q : AffinePoint E) (m : Nat)
    (division : Store (MeasuredPointAddition.context p.size))
    (stored : Store (Context p.size m)) :
    ∃ operator : HilbertOperator (Context p.size m).register,
      ∀ Reference : Register,
        pointMatrix (environment := environment) E Q m Reference division stored =
          operator ⊗ₖ (1 : HilbertOperator Reference) := by
  let inner := Recovery.Point.indexedPointPlacement p.size (0 : Fin 2)
  let outer := Recovery.Point.cellsPlacement (readyContext p.size 2) 2 (2 * m)
  obtain ⟨point, factor⟩ := Recovery.Point.Instrument.pointKraus_reference_factor (environment :=
    environment) E Q division
    (inner.store (outer.store stored).1).1
  let readyOperator := (point ⊗ₖ (1 : HilbertOperator inner.frame.register)).submatrix
    inner.basis inner.basis
  refine ⟨(readyOperator ⊗ₖ (1 : HilbertOperator outer.frame.register)).submatrix
    outer.basis outer.basis, ?_⟩
  intro Reference
  unfold pointMatrix
  dsimp only
  rw [factor, embedded_tensor_identity inner, embedded_tensor_identity outer]

/-- The literal feedback product has a reference-independent operator in its original order. -/
private lemma feedbackMatrix_reference_factor (width m : Nat) (current : Fin (2 * m))
    (stored : Store (Context width m)) (indices : List (Fin (2 * m))) :
    ∃ operator : HilbertOperator (Context width m).register,
      ∀ Reference : Register,
        feedbackMatrix (environment := environment) width m Reference current stored indices =
          operator ⊗ₖ (1 : HilbertOperator Reference) := by
  induction indices with
  | nil =>
      refine ⟨1, ?_⟩
      intro Reference
      simp only [feedbackMatrix, Matrix.one_kronecker_one]
  | cons previous tail ih =>
      obtain ⟨tailOperator, tailFactor⟩ := ih
      by_cases feeds : Recovery.Layout.feeds m previous current
      · let head := ((phaseProgram width m previous current
          (stored.read (.storage (Recovery.Layout.resultCell width m
            previous).toCStorageRef))).matrix environment.quantum)
        refine ⟨tailOperator * head, ?_⟩
        intro Reference
        simp only [feedbackMatrix, tailFactor, feedbackOneMatrix, if_pos feeds,
          Recovery.Point.Instrument.unitary_tensor_identity]
        exact tensor_identity_mul (Local := (Context width m).register)
          (Reference := Reference) tailOperator head
      · refine ⟨tailOperator, ?_⟩
        intro Reference
        simp only [feedbackMatrix, tailFactor, feedbackOneMatrix, if_neg feeds, Matrix.mul_one]

/-- The actual preparation, point, feedback and readout matrices share one full-bank factor. -/
lemma stageMatrix_reference_factor {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (index : Fin (2 * m)) (stored : Store (Context p.size m))
    (outcome : Fin ((Context p.size m).quantumLayout.wire
      (Recovery.Layout.position p.size m 0)).dimension)
    (division : Store (MeasuredPointAddition.context p.size)) :
    ∃ operator : HilbertOperator (Context p.size m).register,
      ∀ Reference : Register,
        stageMatrix (environment := environment) E r points index Reference stored outcome
          division =
          operator ⊗ₖ (1 : HilbertOperator Reference) := by
  obtain ⟨point, pointFactor⟩ := pointMatrix_reference_factor
    (environment := environment) E (points index) m division stored
  obtain ⟨feedback, feedbackFactor⟩ := feedbackMatrix_reference_factor
    (environment := environment) p.size m index stored (Recovery.Layout.order m)
  let reset := (correction p.size m (.finite outcome)).matrix environment.quantum
  let measured : HilbertOperator (Context p.size m).register :=
    ZMeasurement.projector (fun basis => basis (Recovery.Layout.position p.size m 0)) outcome
  let hadamard := ((Gate.singleQubitAt (Context p.size m).quantumLayout .empty Gate.HOp
    (Recovery.Layout.position p.size m 0) (Recovery.Layout.position_qubit p.size m 0)).matrix
      environment.quantum)
  let prepared := (Recovery.Layout.preparation p.size m r (Recovery.Layout.remaining m
    index)).matrix environment.quantum
  refine ⟨(reset * measured * hadamard) * feedback * point * prepared, ?_⟩
  intro Reference
  simp only [stageMatrix, readoutMatrix, preparationMatrix, pointFactor, feedbackFactor,
    Recovery.Point.Instrument.unitary_tensor_identity]
  rw [Recovery.Point.Instrument.projector_tensor_identity
    (Local := (Context p.size m).register) (Reference := Reference)
    (fun basis => basis (Recovery.Layout.position p.size m 0)) outcome]
  simp only [tensor_identity_mul (Local := (Context p.size m).register)
    (Reference := Reference)]
  rfl

/-- Selecting one complete external tag commutes with a reference-independent matrix sandwich. -/
private lemma reference_factor_tag_sandwich {Local Tag Reference : Type}
    [Fintype Local] [Fintype Tag] [Fintype Reference]
    {tagDecision : DecidableEq (Tag × Reference)}
    {referenceDecision : DecidableEq Reference}
    (operator : Matrix Local Local ℂ)
    (density : Matrix (Local × (Tag × Reference)) (Local × (Tag × Reference)) ℂ)
    (tag : Tag) :
    ((operator ⊗ₖ (@Matrix.one (Tag × Reference) ℂ tagDecision _ _).one) * density *
      (operator ⊗ₖ (@Matrix.one (Tag × Reference) ℂ tagDecision _ _).one).conjTranspose).submatrix
        (fun index : Local × Reference => (index.1, (tag, index.2)))
        (fun index : Local × Reference => (index.1, (tag, index.2))) =
      (operator ⊗ₖ (@Matrix.one Reference ℂ referenceDecision _ _).one) *
        density.submatrix
          (fun index : Local × Reference => (index.1, (tag, index.2)))
          (fun index : Local × Reference => (index.1, (tag, index.2))) *
        (operator ⊗ₖ (@Matrix.one Reference ℂ referenceDecision _ _).one).conjTranspose := by
  have tagDecision_eq : tagDecision = Classical.decEq (Tag × Reference) := Subsingleton.elim _ _
  have referenceDecision_eq : referenceDecision = Classical.decEq Reference := Subsingleton.elim _ _
  subst tagDecision referenceDecision
  ext row column
  exact (Recovery.Point.tensor_conjugation_entry operator density
    row.1 column.1 (tag, row.2) (tag, column.2)).trans
      (Recovery.Point.tensor_conjugation_entry operator
        (density.submatrix
          (fun index : Local × Reference => (index.1, (tag, index.2)))
          (fun index : Local × Reference => (index.1, (tag, index.2))))
        row.1 column.1 row.2 column.2).symm

/-- Factoring and selecting the same tag preserve the complete matrix sandwich. -/
private lemma factored_tag_sandwich {Local Tag Reference : Type}
    [Fintype Local] [Fintype Tag] [Fintype Reference]
    {tagDecision : DecidableEq (Tag × Reference)}
    {referenceDecision : DecidableEq Reference}
    (operator : Matrix Local Local ℂ)
    {taggedOperator : Matrix (Local × (Tag × Reference)) (Local × (Tag × Reference)) ℂ}
    {plainOperator : Matrix (Local × Reference) (Local × Reference) ℂ}
    {density : Matrix (Local × (Tag × Reference)) (Local × (Tag × Reference)) ℂ}
    {selected : Matrix (Local × Reference) (Local × Reference) ℂ} (tag : Tag)
    (taggedFactor : taggedOperator =
      operator ⊗ₖ (@Matrix.one (Tag × Reference) ℂ tagDecision _ _).one)
    (plainFactor : plainOperator = operator ⊗ₖ (@Matrix.one Reference ℂ referenceDecision _ _).one)
    (fiber : density.submatrix
      (fun index : Local × Reference => (index.1, (tag, index.2)))
      (fun index : Local × Reference => (index.1, (tag, index.2))) = selected) :
    (taggedOperator * density * taggedOperator.conjTranspose).submatrix
      (fun index : Local × Reference => (index.1, (tag, index.2)))
      (fun index : Local × Reference => (index.1, (tag, index.2))) =
      plainOperator * selected * plainOperator.conjTranspose := by
  subst taggedOperator plainOperator
  exact (reference_factor_tag_sandwich (tagDecision := tagDecision)
    (referenceDecision := referenceDecision) operator density tag).trans
    (congrArg (fun matrix =>
      (operator ⊗ₖ (@Matrix.one Reference ℂ referenceDecision _ _).one) * matrix *
        (operator ⊗ₖ (@Matrix.one Reference ℂ referenceDecision _ _).one).conjTranspose) fiber)

/-- Store selection commutes with the existing mathematical encoding of a classical tag. -/
private lemma encodeOracleTag_filter_store {ctx : RuntimeCtx .quantum}
    {Reference Tag : Register} {Hidden History : Type}
    [Fintype Hidden] [Fintype History]
    (state : State ctx Reference (Hidden × (History × Tag.Index))) (keep : Store ctx → Prop) :
    State.encodeOracleTag (Tag := Tag) (state.filterClassical (fun record => keep record.1)) =
      (State.encodeOracleTag (Tag := Tag) state).filterClassical (fun record => keep record.1) := by
  apply ExecutionState.ext
  rintro ⟨stored, hidden, history⟩
  apply DensityOperator.ext
  ext row column
  rcases row with ⟨left, leftTag, leftReference⟩
  rcases column with ⟨right, rightTag, rightReference⟩
  rw [State.encodeOracleTag_entry (Reference := Reference) (Tag := Tag)
    (state.filterClassical (fun record => keep record.1)) stored hidden history
    leftTag rightTag (left, leftReference) (right, rightReference)]
  by_cases selected : keep stored
  · simp only [ExecutionState.filterClassical_block, if_pos selected]
    exact (State.encodeOracleTag_entry (Reference := Reference) (Tag := Tag) state
      stored hidden history leftTag rightTag (left, leftReference) (right, rightReference)).symm
  · simp only [ExecutionState.filterClassical_block, if_neg selected,
      DensityOperator.zero_matrix, Matrix.zero_apply, ite_self]

/-- The tag slice retains an arbitrary full-Store predicate as well as the original history tag. -/
private lemma encoded_store_tag_fiber {ctx : RuntimeCtx .quantum}
    {Reference Tag : Register} {Hidden History : Type}
    [Fintype Hidden] [Fintype History]
    (state : State ctx Reference (Hidden × (History × Tag.Index)))
    (keep : Store ctx → Prop) (tag : Tag.Index) :
    ((State.encodeOracleTag (Tag := Tag) state).filterClassical
        (fun record => keep record.1)).quantumMarginal.matrix.submatrix
          (fun index : (ctx.register.prod Reference).Index => (index.1, (tag, index.2)))
          (fun index : (ctx.register.prod Reference).Index => (index.1, (tag, index.2))) =
      (state.filterClassical (fun record => keep record.1 ∧ record.2.2.2 =
        tag)).quantumMarginal.matrix
        := by
  rw [← encodeOracleTag_filter_store, Recovery.Point.encodeOracleTag_fiber_matrix,
    filter_intersection_decisions]
  exact Recovery.Point.cells_filter_matrix_predicate_congr state (by
    funext record
    exact propext and_comm)
    (firstDecision := fun _ => inferInstance)
    (secondDecision := fun _ => inferInstance)

/-- Every original history tag remains selected beside the full actual stage Store and Reference. -/
lemma stage_store_retained_fiber {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (index : Fin (2 * m)) {Reference Tag : Register} {History : Type} [Fintype History]
    (state : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × (History × Tag.Index)))
    (stored : Store (Context p.size m)) (tag : Tag.Index) :
    (((stage E r points index).execute environment Reference state).filterClassical
      (fun record => record.1 = stored ∧ record.2.2.1.2 = tag)).quantumMarginal.matrix =
      ∑ intermediate : Store (Context p.size m),
        ∑ outcome : Fin ((Context p.size m).quantumLayout.wire
          (Recovery.Layout.position p.size m 0)).dimension,
          ∑ division : Store (MeasuredPointAddition.context p.size),
            if intermediate.write (output p.size m index) (.finite outcome) = stored then
              stageMatrix (environment := environment) E r points index Reference intermediate
                outcome division *
                (state.filterClassical (fun record =>
                  retains p.size m intermediate record.1 ∧ record.2.2.2 =
                    tag)).quantumMarginal.matrix
                    *
                (stageMatrix (environment := environment) E r points index Reference intermediate
                  outcome division).conjTranspose
            else 0 := by
  rw [(stage E r points index).execute_encodedClassicalTag environment state,
    Recovery.Point.decodeExecutionTag_store_fiber_matrix,
    stage_store_matrix E r points index (Reference := Tag.prod Reference)
      (State.encodeOracleTag (Tag := Tag) state) stored]
  ext row column
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro intermediate _
  apply Finset.sum_congr rfl
  intro outcome _
  apply Finset.sum_congr rfl
  intro division _
  by_cases written : intermediate.write (output p.size m index) (.finite outcome) = stored
  · simp only [if_pos written]
    obtain ⟨operator, factor⟩ :=
      stageMatrix_reference_factor (environment := environment)
        E r points index intermediate outcome division
    have fiber := encoded_store_tag_fiber (ctx := Context p.size m) (Reference := Reference)
      (Tag := Tag) (Hidden := ClassicalOracleModel.empty.HiddenState) (History := History)
      state (fun record => retains p.size m intermediate record) tag
    exact congrArg (fun matrix => matrix row column)
      (factored_tag_sandwich operator tag (factor (Tag.prod Reference)) (factor Reference) fiber)
  · simp only [if_neg written, Matrix.zero_apply]

/-- A finite Boolean tag denotes the existing predicate and adds no physical register. -/
private def predicateTag : Register where
  Index := Bool
  fintype := inferInstance
  decEq := inferInstance

/-- The input tag selects the same complete Store and original-history predicate. -/
private lemma predicate_input_tag_fiber {ctx : RuntimeCtx .quantum}
    {Reference : Register} {Hidden History : Type} [Fintype Hidden] [Fintype History]
    (state : State ctx Reference (Hidden × History))
    (keep : Store ctx → Prop) (predicate : History → Prop) :
    ((state.mapHistory (fun record =>
      (record.1, (record.2, decide (predicate record.2))))).filterClassical
      (fun record => keep record.1 ∧ record.2.2.2 = true)).quantumMarginal.matrix =
      (state.filterClassical (fun record =>
        keep record.1 ∧ predicate record.2.2)).quantumMarginal.matrix := by
  dsimp only [State.mapHistory]
  refine (Recovery.Point.cells_map_filter_matrix_decisions state
    (fun record => (record.1, (record.2.1, (record.2.2, decide (predicate record.2.2)))))
    (fun record => keep record.1 ∧ record.2.2.2 = true)
    (inputDecision := fun _ => inferInstance)).trans ?_
  exact Recovery.Point.cells_filter_matrix_predicate_congr state (by
    funext record
    simp only [decide_eq_true_eq])
    (firstDecision := fun _ => inferInstance)
    (secondDecision := fun _ => inferInstance)

/-- Output tag selection retains the original history and the entire generated Path. -/
private lemma predicate_output_tag_fiber {ctx : RuntimeCtx .quantum}
    {Reference : Register} {Hidden History Path : Type}
    [Fintype Hidden] [Fintype History] [Fintype Path]
    (state : State ctx Reference (Hidden × (History × Path)))
    (stored : Store ctx) (predicate : History → Prop) :
    ((state.mapHistory (fun record =>
      (record.1, ((record.2.1, decide (predicate record.2.1)), record.2.2)))).filterClassical
      (fun record => record.1 = stored ∧ record.2.2.1.2 = true)).quantumMarginal.matrix =
      (state.filterClassical (fun record =>
        record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix := by
  dsimp only [State.mapHistory]
  refine (Recovery.Point.cells_map_filter_matrix_decisions state
    (fun record => (record.1,
      (record.2.1, ((record.2.2.1, decide (predicate record.2.2.1)), record.2.2.2))))
    (fun record => record.1 = stored ∧ record.2.2.1.2 = true)
    (inputDecision := fun _ => inferInstance)).trans ?_
  exact Recovery.Point.cells_filter_matrix_predicate_congr state (by
    funext record
    simp only [decide_eq_true_eq])
    (firstDecision := fun _ => inferInstance)
    (secondDecision := fun _ => inferInstance)

/-- The actual complete stage law at an arbitrary predicate of the original History.

Only generated stage paths are summed; all original full Store, hidden service,
history and quantum/reference data remain in their original coordinates.
-/
lemma stage_store_history_matrix {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (index : Fin (2 * m)) {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (Context p.size m)) (predicate : History → Prop) :
    (((stage E r points index).execute environment Reference state).filterClassical
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ intermediate : Store (Context p.size m),
        ∑ outcome : Fin ((Context p.size m).quantumLayout.wire
          (Recovery.Layout.position p.size m 0)).dimension,
          ∑ division : Store (MeasuredPointAddition.context p.size),
            if intermediate.write (output p.size m index) (.finite outcome) = stored then
              stageMatrix (environment := environment) E r points index Reference intermediate
                outcome division *
                (state.filterClassical (fun record =>
                  retains p.size m intermediate record.1 ∧ predicate
                    record.2.2)).quantumMarginal.matrix
                    *
                (stageMatrix (environment := environment) E r points index Reference intermediate
                  outcome division).conjTranspose
            else 0 := by
  have actual := (stage E r points index).execute_mapHistory environment Reference state
    (fun history => (history, decide (predicate history)))
  have selected := stage_store_retained_fiber (environment := environment) E r points index (Tag
    := predicateTag)
    (state.mapHistory (fun record =>
      (record.1, (record.2, decide (predicate record.2))))) stored (true : Bool)
  have observed := congrArg (fun result : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState ×
        ((History × Bool) × (stage E r points index).Path)) =>
    (result.filterClassical (fun record =>
      record.1 = stored ∧ record.2.2.1.2 = true)).quantumMarginal.matrix) actual
  have selectedMatrix := observed.symm.trans selected
  refine (predicate_output_tag_fiber
    ((stage E r points index).execute environment Reference state) stored predicate).symm.trans
    (selectedMatrix.trans ?_)
  apply Finset.sum_congr rfl
  intro intermediate _
  apply Finset.sum_congr rfl
  intro outcome _
  apply Finset.sum_congr rfl
  intro division _
  by_cases written : intermediate.write (output p.size m index) (.finite outcome) = stored
  · simp only [if_pos written]
    apply congrArg (fun density : HilbertOperator ((Context p.size m).register.prod Reference) =>
      stageMatrix (environment := environment) E r points index Reference intermediate outcome
        division * density *
        (stageMatrix (environment := environment) E r points index Reference intermediate outcome
          division).conjTranspose)
    exact predicate_input_tag_fiber state (retains p.size m intermediate) predicate
  · simp only [if_neg written]

/-- Input density selects both the complete Store and the same original-history predicate. -/
def inputHistoryDensity {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (predicate : History → Prop) (stored : Store ctx) :
    HilbertOperator (ctx.register.prod Reference) :=
  (state.filterClassical (fun record => record.1 = stored ∧ predicate
    record.2.2)).quantumMarginal.matrix

/-- Retention decomposes over every full input Store inside the selected history fiber. -/
private lemma retained_history_density {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference (ClassicalOracleModel.empty.HiddenState × History))
    (keep : Store ctx → Prop) (predicate : History → Prop) :
    (state.filterClassical (fun record => keep record.1 ∧ predicate
      record.2.2)).quantumMarginal.matrix
        =
      ∑ original : Store ctx,
        if keep original then inputHistoryDensity state predicate original else 0 := by
  have full := filter_store_matrix
    (state.filterClassical (fun record => predicate record.2.2)) keep
  simpa only [filter_intersection, inputHistoryDensity] using full

/-- The actual stage applies the original stepDensity to each entire original-history fiber. -/
lemma stage_store_history_density {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (index : Fin (2 * m)) {Reference : Register} {History : Type} [Fintype History]
    (state : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (stored : Store (Context p.size m)) (predicate : History → Prop) :
    (((stage E r points index).execute environment Reference state).filterClassical
      (fun record => record.1 = stored ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      stepDensity (environment := environment) E r points index Reference (inputHistoryDensity
        state predicate) stored := by
  rw [stage_store_history_matrix]
  unfold stepDensity
  apply Finset.sum_congr rfl
  intro intermediate _
  apply Finset.sum_congr rfl
  intro outcome _
  apply Finset.sum_congr rfl
  intro division _
  by_cases written : intermediate.write (output p.size m index) (.finite outcome) = stored
  · rw [if_pos written, if_pos written, retained_history_density]
  · rw [if_neg written, if_neg written]

/-- The actual multi-stage interpreter expands into the original complete legal-path CP sum.

Every generated Path reassociation is the literal execute_seq reassociation.
The input predicate always reads the original History coordinate, never a
generated path or a final measured Store. The zero-length case is the actual
identity law, and no zero CP summand is removed.
-/
lemma actual_trace_history_density {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (length : Nat) (indices : Fin length → Fin (2 * m))
    {History : Type} [Fintype History]
    (state : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (Context p.size m)) (predicate : History → Prop) :
    (((stages E r points (List.ofFn indices)).execute environment Reference state).filterClassical
      (fun record => record.1 = final ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      PathDensity.traceDensity (environment := environment) E r points Reference length indices
        (inputHistoryDensity state predicate) final := by
  induction length generalizing History with
  | zero =>
      exact (HistoryMatrices.id_store_history_matrix
        (model := .quantum AlgorithmGate.model .empty) (allowAllocation := false)
        state final predicate).trans
          (PathDensity.traceDensity_zero E r points Reference indices
            (inputHistoryDensity state predicate) final).symm
  | succ length ih =>
      rw [List.ofFn_succ]
      have sequential := HistoryMatrices.seq_store_history_matrix (environment := environment)
        (stage E r points (indices 0))
        (stages E r points (List.ofFn (Fin.tail indices))) state final predicate
      refine sequential.trans ?_
      have continued := ih (Fin.tail indices)
        ((stage E r points (indices 0)).execute environment Reference state)
        (fun history : History × (stage E r points (indices 0)).Path => predicate history.1)
      refine continued.trans ?_
      rw [PathDensity.traceDensity_succ]
      have first :
          inputHistoryDensity ((stage E r points (indices 0)).execute environment Reference state)
              (fun history => predicate history.1) =
            stepDensity (environment := environment) E r points (indices 0) Reference
              (inputHistoryDensity state predicate) := by
        funext original
        exact stage_store_history_density E r points (indices 0) state original predicate
      rw [first]

/-- Selecting the original History at the output equals filtering that same input fiber first.

This transports the actual input for applying existing initialized/Fourier
laws to the filtered state. Their original initialization equality remains
required; no new admission certificate is imposed on the original caller.
-/
lemma actual_trace_history_filter_input {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (length : Nat) (indices : Fin length → Fin (2 * m))
    {History : Type} [Fintype History]
    (state : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (Context p.size m)) (predicate : History → Prop) :
    (((stages E r points (List.ofFn indices)).execute environment Reference state).filterClassical
      (fun record => record.1 = final ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      storeDensity ((stages E r points (List.ofFn indices)).execute environment Reference
        (state.filterClassical (fun record => predicate record.2.2))) final := by
  rw [actual_trace_history_density, PathDensity.actual_trace_density]
  have inputSame : inputHistoryDensity state predicate =
      storeDensity (state.filterClassical (fun record => predicate record.2.2)) := by
    funext original
    simp only [inputHistoryDensity, storeDensity, filter_intersection]
  rw [inputSame]

/-- The exact full legal-path CP expansion retains every original History predicate. -/
lemma full_legal_history_paths {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) {History : Type} [Fintype History]
    (state : State (Context p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (Context p.size m)) (predicate : History → Prop) :
    (((stages E r points (Recovery.Layout.order m)).execute environment Reference
      state).filterClassical
      (fun record => record.1 = final ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      ∑ path : Fin (2 * m) → PathDensity.Branch p.size m,
        ∑ original : Store (Context p.size m),
          if PathDensity.traceValid p.size m (2 * m) id path original final then
            pathProduct (environment := environment) E r points Reference (fun index => (path
              index).2.2)
                (fun index => (path index).1) (fun index => (path index).2.1)
                (Recovery.Layout.order m) * inputHistoryDensity state predicate original *
              (pathProduct (environment := environment) E r points Reference (fun index => (path
                index).2.2)
                (fun index => (path index).1) (fun index => (path index).2.1)
                (Recovery.Layout.order m)).conjTranspose
          else 0 := by
  have actual := actual_trace_history_density (environment := environment) E r points Reference (2
    * m) id state final predicate
  change (((stages E r points (Recovery.Layout.order m)).execute environment Reference
    state).filterClassical
    (fun record => record.1 = final ∧ predicate record.2.2.1)).quantumMarginal.matrix =
      PathDensity.traceDensity (environment := environment) E r points Reference (2 * m) id
        (inputHistoryDensity state predicate) final at actual
  rw [actual]
  unfold PathDensity.traceDensity
  apply Finset.sum_congr rfl
  intro path _
  have product := PathDensity.traceKraus_of_indexed_path (environment := environment) E r points
    Reference path (2 * m) id
  change PathDensity.traceKraus (environment := environment) E r points Reference (2 * m) id path =
    pathProduct (environment := environment) E r points Reference (fun index => (path index).2.2)
      (fun index => (path index).1) (fun index => (path index).2.1)
      (Recovery.Layout.order m) at product
  simp only [product]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.HistoryPaths

