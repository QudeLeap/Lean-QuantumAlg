/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Path.Word
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.WordRecursion
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Rows
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Execution
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Point.Program
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.History.Feedback
import all Mathlib.Data.Fin.Tuple.Basic
import all QuantumAlg.Util.Matrix.Trace.Step

/-!
# Actual full-Store legal-path density expansion

Complete Store, dirty bank, arbitrary external Reference and original arithmetic factor
order are retained.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
namespace PointCoordinates.StageWord.PathWord.PathDensity

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open StoredRecursion
open scoped BigOperators Kronecker


local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

def traceKraus
    {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}
    {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register) :
    (count : Nat) → (Fin count → Fin (2 * m)) → (Fin count → Branch p.size m) →
      Matrix ((Interface p.size m).register.prod Reference).Index
        ((Interface p.size m).register.prod Reference).Index ℂ
  | 0, _, _ => 1
  | count + 1, indices, path =>
      traceKraus (environment := environment) E r points Reference count (Fin.tail indices)
        (Fin.tail path) *
        stageMatrix (environment := environment) E r points (indices 0) Reference (path 0).1 (path
          0).2.1 (path 0).2.2

def traceDensity {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (count : Nat) (indices : Fin count → Fin (2 * m))
    (density : Store (Interface p.size m) →
      Matrix ((Interface p.size m).register.prod Reference).Index
        ((Interface p.size m).register.prod Reference).Index ℂ)
    (final : Store (Interface p.size m)) :
    Matrix ((Interface p.size m).register.prod Reference).Index
      ((Interface p.size m).register.prod Reference).Index ℂ :=
  ∑ path : Fin count → Branch p.size m,
    ∑ original : Store (Interface p.size m),
      if traceValid p.size m count indices path original final then
        traceKraus (environment := environment) E r points Reference count indices path * density
          original *
          (traceKraus (environment := environment) E r points Reference count indices
            path).conjTranspose
      else 0

private lemma stepDensity_branches {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (index : Fin (2 * m))
    (density : Store (Interface p.size m) →
      Matrix ((Interface p.size m).register.prod Reference).Index
        ((Interface p.size m).register.prod Reference).Index ℂ)
    (stored : Store (Interface p.size m)) :
    stepDensity (environment := environment) E r points index Reference density stored =
      ∑ branch : Branch p.size m,
        if written p.size m index branch = stored then
          stageMatrix (environment := environment) E r points index Reference branch.1 branch.2.1
            branch.2.2 *
            (∑ original : Store (Interface p.size m),
              if retains p.size m branch.1 original then density original else 0) *
              (stageMatrix (environment := environment) E r points index Reference branch.1
                branch.2.1
                branch.2.2).conjTranspose
        else 0 := by
  simp only [stepDensity, written, Fintype.sum_prod_type]

private lemma traceDensity_zero {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (indices : Fin 0 → Fin (2 * m))
    (density : Store (Interface p.size m) →
      Matrix ((Interface p.size m).register.prod Reference).Index
        ((Interface p.size m).register.prod Reference).Index ℂ)
    (final : Store (Interface p.size m)) :
    traceDensity (environment := environment) E r points Reference 0 indices density final =
      density final := by
  simp only [traceDensity, traceValid, traceKraus, Matrix.one_mul, Matrix.mul_one,
    Matrix.conjTranspose_one, Fintype.sum_ite_eq', Fintype.sum_unique]

section

-- Finite path sums use the established stage operators without reducing their circuits.
attribute [local irreducible] Circuit.pathFintype stageMatrix stepDensity traceDensity traceKraus
  traceValid

private lemma traceDensity_succ {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (count : Nat) (indices : Fin (count + 1) → Fin (2 * m))
    (density : Store (Interface p.size m) →
      Matrix ((Interface p.size m).register.prod Reference).Index
        ((Interface p.size m).register.prod Reference).Index ℂ)
    (final : Store (Interface p.size m)) :
    traceDensity (environment := environment) E r points Reference (count + 1) indices density
      final =
      traceDensity (environment := environment) E r points Reference count (Fin.tail indices)
        (stepDensity (environment := environment) E r points (indices 0) Reference density) final
          := by
  unfold traceDensity
  have expanded := MatrixTrace.sum_cons
    (StoreIndex := Store (Interface p.size m)) (BranchIndex := Branch p.size m)
    (QuantumIndex := ((Interface p.size m).register.prod Reference).Index) count
    (fun branch => stageMatrix (environment := environment) E r points (indices 0) Reference
      branch.1 branch.2.1 branch.2.2)
    (written p.size m (indices 0)) (fun branch => retains p.size m branch.1)
    (traceKraus (environment := environment) E r points Reference count (Fin.tail indices))
    (fun path original => traceValid p.size m count (Fin.tail indices) path original final)
    density (stepDensity (environment := environment) E r points (indices 0) Reference density)
    (stepDensity_branches E r points Reference (indices 0) density)
  simpa only [traceValid, traceKraus] using expanded

end

lemma actual_trace_density {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    (count : Nat) (indices : Fin count → Fin (2 * m)) {History : Type} [Fintype History]
    (state : State (Interface p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (final : Store (Interface p.size m)) :
    storeDensity ((stages E r points (List.ofFn indices)).execute environment Reference state)
      final =
      traceDensity (environment := environment) E r points Reference count indices (storeDensity
        state) final := by
  induction count generalizing History with
  | zero =>
      exact (id_store_matrix state final).trans
        (traceDensity_zero E r points Reference indices (storeDensity state) final).symm
  | succ count ih =>
      rw [List.ofFn_succ]
      have sequential := congrArg DensityOperator.matrix
        (Circuit.seq_store_marginal (environment := environment) (stage E r points (indices 0))
          (stages E r points (List.ofFn (Fin.tail indices))) state final)
      refine sequential.trans ?_
      change storeDensity
          ((stages E r points (List.ofFn (Fin.tail indices))).execute environment Reference
            ((stage E r points (indices 0)).execute environment Reference state)) final = _
      rw [ih, traceDensity_succ]
      have first : storeDensity ((stage E r points (indices 0)).execute environment Reference
        state) =
          stepDensity (environment := environment) E r points (indices 0) Reference (storeDensity
            state) := by
        funext original
        exact stage_store_density E r points (indices 0) state original
      rw [first]

private lemma traceKraus_of_indexed_path {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (Reference : Register) (path : Fin (2 * m) → Branch p.size m)
    (count : Nat) (indices : Fin count → Fin (2 * m)) :
    traceKraus (environment := environment) E r points Reference count indices (fun position =>
      path (indices position)) =
      pathProduct (environment := environment) E r points Reference (fun index => (path index).2.2)
        (fun index => (path index).1) (fun index => (path index).2.1) (List.ofFn indices) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [traceKraus, List.ofFn_succ, pathProduct]
      change traceKraus (environment := environment) E r points Reference count (Fin.tail indices)
          (fun position => path (Fin.tail indices position)) *
          stageMatrix (environment := environment) E r points (indices 0) Reference
            (path (indices 0)).1 (path (indices 0)).2.1 (path (indices 0)).2.2 = _
      rw [ih]
      rfl

lemma full_instrument_paths {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State (Interface p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History)) (final : Store (Interface p.size m)) :
    storeDensity ((stages E r points (Recovery.Layout.order m)).execute environment Reference
      state) final =
      ∑ path : Fin (2 * m) → Branch p.size m,
        ∑ original : Store (Interface p.size m),
          if traceValid p.size m (2 * m) id path original final then
            pathProduct (environment := environment) E r points Reference (fun index => (path
              index).2.2)
                (fun index => (path index).1) (fun index => (path index).2.1)
                (Recovery.Layout.order m) * storeDensity state original *
              (pathProduct (environment := environment) E r points Reference (fun index => (path
                index).2.2)
                (fun index => (path index).1) (fun index => (path index).2.1)
                (Recovery.Layout.order m)).conjTranspose
          else 0 := by
  have actual := actual_trace_density (environment := environment) E r points Reference (2 * m) id
    state final
  change storeDensity ((stages E r points (Recovery.Layout.order m)).execute environment Reference
    state)
    final =
    traceDensity (environment := environment) E r points Reference (2 * m) id (storeDensity state)
      final at actual
  rw [actual]
  unfold traceDensity
  apply Finset.sum_congr rfl
  intro path _
  have product := traceKraus_of_indexed_path (environment := environment) E r points Reference
    path (2 * m) id
  change traceKraus (environment := environment) E r points Reference (2 * m) id path =
    pathProduct (environment := environment) E r points Reference (fun index => (path index).2.2)
      (fun index => (path index).1) (fun index => (path index).2.1)
      (Recovery.Layout.order m) at product
  simp only [product]

end

end PointCoordinates.StageWord.PathWord.PathDensity
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Stage
