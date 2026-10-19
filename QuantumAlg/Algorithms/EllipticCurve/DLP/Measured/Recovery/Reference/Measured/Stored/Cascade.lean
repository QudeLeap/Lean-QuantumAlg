/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Reference.Measured.Stored.Step
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.WordRecursion
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Path.Density
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication.Measured.Cascade
import all QuantumAlg.Core.Execution.Composition.Laws
import all QuantumAlg.Core.Execution.Store.MarginalSum
import all Mathlib.Data.Fin.Tuple.Basic

/-!
# Actual old scalar cascade as a complete-Store Kraus decomposition

The production cascade executes its production indexed steps. Each coarse arithmetic
path contributes one full-register sandwich with the same division/final Store labels on
ket and bra. Quantum exponent entries are never selected by a classical predicate. No
good-domain, arithmetic commutation, product-state or clean-bank premise is used.
Fourier gates, conversions, DLP allocators and terminal readout are absent.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
namespace Measured

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open ScalarMultiplication.MeasuredPlacement Recovery.Point
open Recovery.Stage.PointCoordinates.StageWord.StoredRecursion
  (filter_store_matrix)
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity
  (sum_at_condition sandwich_sum collapse_written_sum retained_sandwich)
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- This records a full physical density fiber; it does not observe any exponent. -/
def storeDensity {ctx : RuntimeCtx .quantum} {Reference : Register}
    {History : Type} [Fintype History] (state : State ctx Reference History)
    (stored : Store ctx) :
    Matrix (ctx.register.prod Reference).Index (ctx.register.prod Reference).Index ℂ :=
  (state.filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix

private lemma filter_store_matrix_decision {ctx : RuntimeCtx .quantum}
    {Reference : Register} {History : Type} [Fintype History]
    (state : State ctx Reference History) (predicate : Store ctx → Prop)
    {decision : DecidablePred (fun record : Store ctx × History => predicate record.1)} :
    (@ExecutionState.filterClassical (Store ctx × History) _ (ctx.register.prod Reference)
      state (fun record => predicate record.1) decision).quantumMarginal.matrix =
      ∑ stored : Store ctx, if predicate stored then
        (state.filterClassical (fun record => record.1 = stored)).quantumMarginal.matrix
      else 0 := by
  cases Subsingleton.elim decision
    (fun record => Classical.propDecidable (predicate record.1))
  exact filter_store_matrix state predicate

/-- Only the actual ambient classical Store is retained across the old point call. -/
def retains (width : Nat) {count : Nat} (active : Fin count)
    (final original : Store (readyContext width count)) : Prop :=
  (pointStore width active original).2 = (pointStore width active final).2

def stepDensity {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (active : Fin count)
    (Reference : Register)
    (density : Store (readyContext p.size count) →
      Matrix ((readyContext p.size count).register.prod Reference).Index
        ((readyContext p.size count).register.prod Reference).Index ℂ)
    (final : Store (readyContext p.size count)) :
    Matrix ((readyContext p.size count).register.prod Reference).Index
      ((readyContext p.size count).register.prod Reference).Index ℂ :=
  ∑ division : Store (MeasuredPointAddition.context p.size),
    stepKraus (environment := environment) E (points active) active Reference division final *
      (∑ original : Store (readyContext p.size count),
        if retains p.size active final original then density original else 0) *
      (stepKraus (environment := environment) E (points active) active Reference division
        final).conjTranspose

/-- The one-step decomposition is about the actual interpreter on all dirty inputs. -/
lemma actual_step_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (active : Fin count)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (readyContext p.size count)) (allowAllocation : Bool := true) :
    storeDensity ((step E (points active) active allowAllocation).execute environment Reference
      state) final =
      stepDensity (environment := environment) E points active Reference (storeDensity state)
        final := by
  have actual := step_store_history_matrix (environment := environment)
    E (points active) active state final
    (fun _ => True) allowAllocation
  simp only [and_true] at actual
  refine actual.trans ?_
  unfold stepDensity
  apply Finset.sum_congr rfl
  intro division _
  rw [filter_store_matrix_decision state
    (fun original => (pointStore p.size active original).2 = (pointStore p.size active final).2)]
  rfl

/-- Each real coarse arithmetic branch remembers its complete post-point Store and division. -/
abbrev Branch (width count : Nat) :=
  Store (readyContext width count) × Store (MeasuredPointAddition.context width)

/-- The chronological product is tail times head, without exchanging any point factor. -/
def traceKraus
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register) :
    (length : Nat) → (Fin length → Fin count) → (Fin length → Branch p.size count) →
      Matrix ((readyContext p.size count).register.prod Reference).Index
        ((readyContext p.size count).register.prod Reference).Index ℂ
  | 0, _, _ => 1
  | length + 1, indices, path =>
      traceKraus (environment := environment) E points Reference length (Fin.tail indices)
        (Fin.tail path) *
        stepKraus (environment := environment) E (points (indices 0)) (indices 0) Reference (path
          0).2 (path 0).1

/-- Legal complete Stores retain exactly the actual classical frame at every call. -/
def traceValid (width : Nat) {count : Nat} :
    (length : Nat) → (Fin length → Fin count) → (Fin length → Branch width count) →
      Store (readyContext width count) → Store (readyContext width count) → Prop
  | 0, _, _, original, final => original = final
  | length + 1, indices, path, original, final =>
      retains width (indices 0) (path 0).1 original ∧
        traceValid width length (Fin.tail indices) (Fin.tail path) (path 0).1 final

/-- Histories are summed after each sandwich, with a single common path on ket and bra. -/
def traceDensity {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register)
    (length : Nat) (indices : Fin length → Fin count)
    (density : Store (readyContext p.size count) →
      Matrix ((readyContext p.size count).register.prod Reference).Index
        ((readyContext p.size count).register.prod Reference).Index ℂ)
    (final : Store (readyContext p.size count)) :
    Matrix ((readyContext p.size count).register.prod Reference).Index
      ((readyContext p.size count).register.prod Reference).Index ℂ :=
  ∑ path : Fin length → Branch p.size count,
    ∑ original : Store (readyContext p.size count),
      if traceValid p.size length indices path original final then
        traceKraus (environment := environment) E points Reference length indices path * density
          original *
          (traceKraus (environment := environment) E points Reference length indices
            path).conjTranspose
      else 0

private lemma traceDensity_zero {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register)
    (indices : Fin 0 → Fin count)
    (density : Store (readyContext p.size count) →
      Matrix ((readyContext p.size count).register.prod Reference).Index
        ((readyContext p.size count).register.prod Reference).Index ℂ)
    (final : Store (readyContext p.size count)) :
    traceDensity (environment := environment) E points Reference 0 indices density final = density
      final := by
  simp only [traceDensity, traceValid, traceKraus, Matrix.one_mul, Matrix.mul_one,
    Matrix.conjTranspose_one, Fintype.sum_ite_eq', Fintype.sum_unique]

private lemma sum_fst_selection {I Division J : Type} [Fintype I] [Fintype Division]
    (value : I × Division → Matrix J J ℂ) (original : I) :
    (∑ branch : I × Division, if branch.1 = original then value branch else 0) =
      ∑ division : Division, value (original, division) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fintype.sum_ite_eq']

private lemma collapse_fst_sum {I Division J : Type}
    [Fintype I] [Fintype Division] [Fintype J]
    (operator : Matrix J J ℂ) (follows : I → Prop)
    (value : I × Division → Matrix J J ℂ) :
    (∑ original : I, if follows original then
      operator * (∑ division : Division, value (original, division)) *
        operator.conjTranspose else 0) =
      ∑ branch : I × Division, if follows branch.1 then
        operator * value branch * operator.conjTranspose else 0 := by
  exact collapse_written_sum operator follows Prod.fst value
    (fun original => ∑ division : Division, value (original, division))
    (fun original => (sum_fst_selection value original).symm)

/-- Expand one actual old point call, preserving multiplicities of the complete Store paths. -/
private lemma traceDensity_succ {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register)
    (length : Nat) (indices : Fin (length + 1) → Fin count)
    (density : Store (readyContext p.size count) →
      Matrix ((readyContext p.size count).register.prod Reference).Index
        ((readyContext p.size count).register.prod Reference).Index ℂ)
    (final : Store (readyContext p.size count)) :
    traceDensity (environment := environment) E points Reference (length + 1) indices density
      final =
      traceDensity (environment := environment) E points Reference length (Fin.tail indices)
        (stepDensity (environment := environment) E points (indices 0) Reference density) final :=
          by
  unfold traceDensity
  rw [← (Fin.consEquiv (fun _ : Fin (length + 1) => Branch p.size count)).sum_comp,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Fin.consEquiv_apply, traceValid, traceKraus, Fin.cons_zero]
  apply Finset.sum_congr rfl
  intro tail _
  let operator := traceKraus (environment := environment) E points Reference length (Fin.tail
    indices) tail
  let follows := fun original : Store (readyContext p.size count) =>
    traceValid p.size length (Fin.tail indices) tail original final
  let value := fun branch : Branch p.size count =>
    stepKraus (environment := environment) E (points (indices 0)) (indices 0) Reference branch.2
      branch.1 *
      (∑ original : Store (readyContext p.size count),
        if retains p.size (indices 0) branch.1 original then density original else 0) *
      (stepKraus (environment := environment) E (points (indices 0)) (indices 0) Reference
        branch.2 branch.1).conjTranspose
  have collapsed := collapse_fst_sum operator follows value
  refine Eq.trans (b := ∑ branch : Branch p.size count,
    if follows branch.1 then operator * value branch * operator.conjTranspose else 0)
    ?_ collapsed.symm
  apply Finset.sum_congr rfl
  intro branch _
  have tailSame :
      Fin.tail ((Fin.consEquiv (fun _ : Fin (length + 1) => Branch p.size count))
        (branch, tail)) = tail := by
    change Fin.tail (Fin.cons
      (α := fun _ : Fin (length + 1) => Branch p.size count) branch tail) = tail
    exact Fin.tail_cons (n := length)
      (α := fun _ : Fin (length + 1) => Branch p.size count) branch tail
  rw [tailSame]
  exact retained_sandwich operator
    (stepKraus (environment := environment) E (points (indices 0)) (indices 0) Reference branch.2
      branch.1)
    (retains p.size (indices 0) branch.1) (follows branch.1) density

/-- Complete original cascade execution before Fourier and conversion boundaries. -/
lemma actual_cascade_store_density {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register)
    (length : Nat) (indices : Fin length → Fin count) {History : Type} [Fintype History]
    (state : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (readyContext p.size count)) (allowAllocation : Bool := true) :
    storeDensity ((cascade E points (List.ofFn indices) allowAllocation).execute environment
      Reference state) final =
      traceDensity (environment := environment) E points Reference length indices (storeDensity
        state) final := by
  induction length generalizing History with
  | zero =>
      have identity :
          storeDensity ((cascade E points (List.ofFn indices) allowAllocation).execute environment
            Reference state) final =
            storeDensity state final := by
        change (((Circuit.id (allowAllocation := allowAllocation)
          (model := .quantum AlgorithmGate.model .empty)
          (readyContext p.size count)).execute environment Reference state).filterClassical
            (fun record => record.1 = final)).quantumMarginal.matrix = _
        rw [Circuit.execute_id]
        exact cells_map_filter_matrix_decisions state
          (fun entry => (entry.1, entry.2.1, entry.2.2, ()))
          (fun record => record.1 = final)
      exact identity.trans (traceDensity_zero E points Reference indices
        (storeDensity state) final).symm
  | succ length ih =>
      rw [List.ofFn_succ]
      have sequential := congrArg DensityOperator.matrix
        (Circuit.seq_store_marginal (environment := environment)
          (step E (points (indices 0)) (indices 0) allowAllocation)
          (cascade E points (List.ofFn (Fin.tail indices)) allowAllocation) state final)
      refine sequential.trans ?_
      change storeDensity
          ((cascade E points (List.ofFn (Fin.tail indices)) allowAllocation).execute environment
            Reference
            ((step E (points (indices 0)) (indices 0) allowAllocation).execute environment
              Reference state)) final = _
      rw [ih, traceDensity_succ]
      have first : storeDensity ((step E (points (indices 0)) (indices 0) allowAllocation).execute
        environment Reference state) = stepDensity (environment := environment) E points (indices
          0) Reference (storeDensity
        state) := by
        funext original
        exact actual_step_density E points (indices 0) state original allowAllocation
      rw [first]

/-- The complete original increasing-index cascade has this actual stored decomposition. -/
lemma actual_fullCascade_store_density {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {count : Nat} (points : Fin count → AffinePoint E) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (readyContext p.size count) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (readyContext p.size count)) (allowAllocation : Bool := true) :
    storeDensity ((fullCascade E points allowAllocation).execute environment Reference state)
      final =
      ∑ path : Fin count → Branch p.size count,
        ∑ original : Store (readyContext p.size count),
          if traceValid p.size count id path original final then
            traceKraus (environment := environment) E points Reference count id path *
              storeDensity state original *
              (traceKraus (environment := environment) E points Reference count id
                path).conjTranspose
          else 0 := by
  have actual := actual_cascade_store_density (environment := environment)
    E points Reference count id state final
    allowAllocation
  change storeDensity ((fullCascade E points allowAllocation).execute environment Reference state)
    final =
    traceDensity (environment := environment) E points Reference count id (storeDensity state)
      final at actual
  exact actual

end

end Measured
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Reference
