/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Conversion.Placement
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Stage.Path.Density
import all QuantumAlg.Util.Matrix.Trace.Convert

/-!
# A literal allocation-free four-conversion wrapper around the actual streaming stages

This wrapper is constructed explicitly from direct native unitary placements. Every
original complete Store and measured path survives the actual CP expansion. No old/new
terminal equality is assumed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty).Environment}

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve
open ScalarMultiplication.MeasuredPlacement
open Recovery.Stage.PointCoordinates
open Recovery.Stage.PointCoordinates.StageWord.StoredRecursion
open Recovery.Stage.PointCoordinates.StageWord.PathWord.PathDensity
open scoped BigOperators

local instance {α : Type} : DecidableEq α := Classical.decEq α
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

/-- Two inverse coordinate invocations, the real stages, then two forward coordinate invocations. -/
def convertedStages {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] {m : Nat}
    (r : Nat) (points : Fin (2 * m) → AffinePoint E) (order : List (Fin (2 * m)))
    (coefficient : (ZMod p)ˣ) :
    Circuit (.quantum AlgorithmGate.model .empty)
      (Recovery.Layout.terminal p.size m) (Recovery.Layout.terminal p.size m) false :=
  (pairCircuit p.size m (InPlaceTarget.modulusWord p) coefficient⁻¹).seq
    ((Recovery.Stage.stages E r points order).seq
      (pairCircuit p.size m (InPlaceTarget.modulusWord p) coefficient))

/-- The actual conversion factors surround one unchanged streaming measurement path. -/
def convertedTraceKraus {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E) (coefficient : (ZMod p)ˣ)
    (Reference : Register) (count : Nat) (indices : Fin count → Fin (2 * m))
    (path : Fin count → Branch p.size m) :
    Matrix ((Recovery.Layout.terminal p.size m).register.prod Reference).Index
      ((Recovery.Layout.terminal p.size m).register.prod Reference).Index ℂ :=
  pairOperator (environment := environment)
    p.size m (InPlaceTarget.modulusWord p) coefficient Reference *
    traceKraus (environment := environment) E r points Reference count indices path *
    pairOperator (environment := environment)
      p.size m (InPlaceTarget.modulusWord p) coefficient⁻¹ Reference

/-- All four actual native multiplier calls stay literal and keep their original order. -/
lemma convertedTraceKraus_four_factors {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register) (count : Nat)
    (indices : Fin count → Fin (2 * m)) (path : Fin count → Branch p.size m) :
    convertedTraceKraus (environment := environment) E r points coefficient Reference count
      indices path =
      (coordinateOperator (environment := environment)
        p.size m (InPlaceTarget.modulusWord p) coefficient .y Reference :
        Matrix _ _ ℂ) *
      (coordinateOperator (environment := environment)
        p.size m (InPlaceTarget.modulusWord p) coefficient .x Reference :
        Matrix _ _ ℂ) * traceKraus (environment := environment) E r points Reference count indices
          path *
      (coordinateOperator (environment := environment)
        p.size m (InPlaceTarget.modulusWord p) coefficient⁻¹ .y Reference :
        Matrix _ _ ℂ) *
      (coordinateOperator (environment := environment)
        p.size m (InPlaceTarget.modulusWord p) coefficient⁻¹ .x Reference :
        Matrix _ _ ℂ) := by
  simp only [convertedTraceKraus, pairOperator, Matrix.mul_assoc]

/-- Compose the actual inverse, path instrument and forward conversion before finite algebra. -/
private lemma convertedStages_prepared_density {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register) (count : Nat)
    (indices : Fin count → Fin (2 * m)) {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (Recovery.Layout.terminal p.size m)) :
    storeDensity ((convertedStages E r points (List.ofFn indices) coefficient).execute environment
      Reference state) final =
      pairOperator (environment := environment) p.size m (InPlaceTarget.modulusWord p)
          coefficient Reference *
        traceDensity (environment := environment) E r points Reference count indices
          (storeDensity ((pairCircuit p.size m (InPlaceTarget.modulusWord p) coefficient⁻¹).execute
            environment Reference state)) final *
        (pairOperator (environment := environment) p.size m (InPlaceTarget.modulusWord p)
          coefficient Reference).conjTranspose := by
  let inverse := pairCircuit p.size m (InPlaceTarget.modulusWord p) coefficient⁻¹
  let forward := pairCircuit p.size m (InPlaceTarget.modulusWord p) coefficient
  let body := Recovery.Stage.stages E r points (List.ofFn indices)
  have outer := congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (environment := environment) inverse (body.seq forward) state final)
  have inner := congrArg DensityOperator.matrix
    (Circuit.seq_store_marginal (environment := environment)
      body forward (inverse.execute environment Reference state) final)
  change storeDensity ((convertedStages E r points (List.ofFn indices) coefficient).execute
    environment Reference state) final =
      storeDensity ((body.seq forward).execute environment Reference (inverse.execute environment
        Reference state)) final
      at outer
  change storeDensity ((body.seq forward).execute environment Reference
    (inverse.execute environment Reference state)) final =
    storeDensity (forward.execute environment Reference
      (body.execute environment Reference
        (inverse.execute environment Reference state))) final at inner
  let operator := pairOperator (environment := environment)
    p.size m (InPlaceTarget.modulusWord p) coefficient Reference
  refine (outer.trans inner).trans
    ((pair_store_density p.size m (InPlaceTarget.modulusWord p) coefficient Reference
      (body.execute environment Reference (inverse.execute environment Reference state))
        final).trans ?_)
  exact congrArg
    (fun density : Matrix ((Recovery.Layout.terminal p.size m).register.prod Reference).Index
        ((Recovery.Layout.terminal p.size m).register.prod Reference).Index ℂ =>
      operator * density * operator.conjTranspose)
    (actual_trace_density E r points Reference count indices
      (inverse.execute environment Reference state) final)

/-- Actual four-conversion streaming execution preserves the complete original Store CP fibers. -/
lemma actual_convertedStages_store_density {p : Nat} (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] {m : Nat} (r : Nat) (points : Fin (2 * m) → AffinePoint E)
    (coefficient : (ZMod p)ˣ) (Reference : Register) (count : Nat)
    (indices : Fin count → Fin (2 * m)) {History : Type} [Fintype History]
    (state : State (Recovery.Layout.terminal p.size m) Reference
      (ClassicalOracleModel.empty.HiddenState × History))
    (final : Store (Recovery.Layout.terminal p.size m)) :
    storeDensity ((convertedStages E r points (List.ofFn indices) coefficient).execute environment
      Reference state) final =
      ∑ path : Fin count → Branch p.size m,
        ∑ original : Store (Recovery.Layout.terminal p.size m),
          if traceValid p.size m count indices path original final then
            convertedTraceKraus (environment := environment) E r points coefficient Reference
              count indices path *
              storeDensity state original *
              (convertedTraceKraus (environment := environment) E r points coefficient Reference
                count indices path).conjTranspose
          else 0 := by
  have prepared := convertedStages_prepared_density (environment := environment)
    E r points coefficient Reference count indices state final
  have algebra := MatrixTrace.sandwich_sum_of_prepared
    (Path := Fin count → Branch p.size m)
    (Store := Store (Recovery.Layout.terminal p.size m))
    (Index := ((Recovery.Layout.terminal p.size m).register.prod Reference).Index)
    (pairOperator (environment := environment) p.size m (InPlaceTarget.modulusWord p)
      coefficient Reference)
    (pairOperator (environment := environment) p.size m (InPlaceTarget.modulusWord p)
      coefficient⁻¹ Reference)
    (traceKraus (environment := environment) E r points Reference count indices)
    (fun path original => traceValid p.size m count indices path original final)
    (storeDensity ((pairCircuit p.size m (InPlaceTarget.modulusWord p) coefficient⁻¹).execute
      environment Reference state)) (storeDensity state)
    (fun original => pair_store_density (environment := environment) p.size m
      (InPlaceTarget.modulusWord p) coefficient⁻¹ Reference state original)
  exact prepared.trans (by
    simpa only [traceDensity, convertedTraceKraus] using algebra)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.Conversion
