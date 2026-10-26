/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Locality.Source.Named.Read

/-!
# Original nominal point cells after the actual measured window

Neither the real table builder's working words nor the point and Fourier
feedback cells have the nominal elliptic-curve-point shape. Consequently
every actual returned record preserves the entire original stored point.
This concerns an actual storage cell; structural input adapters must use
their original stored source when applying it.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling

namespace Locality

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution ClassicalAlgorithms.Modular
open ClassicalRoutines.EllipticCurve.WindowTables

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] NamedDriverPreservesRead NamedMiddlePreservesRead

/-- The actual constructed-table Driver retains an entire original nominal point cell. -/
lemma namedDriverInstrument_point_read (parameters : Driver.Parameters ctx)
    (frame : Outer.Frame ctx 256) (spec : ModulusSpec 256) (row : Fin 34)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {width : Nat} (observed : CStorageRef ctx (.ellipticCurvePoint width)) :
    NamedDriverPreservesRead parameters frame spec row environment observed := by
  apply namedDriverInstrument_read_separate
  · intro key written
    simp only [frameWorkKeys, List.mem_cons, List.not_mem_nil, or_false] at written
    rcases written with rfl | rfl | rfl | rfl
    all_goals exact write_shape_key_ne _ observed (by intro impossible; cases impossible)
  · exact fun _ => write_shape_key_ne _ observed (by intro impossible; cases impossible)
  · exact write_shape_key_ne _ observed (by intro impossible; cases impossible)
  · exact fun _ => write_shape_key_ne _ observed (by intro impossible; cases impossible)
  · exact write_shape_key_ne _ observed (by intro impossible; cases impossible)

/-- The same original point value survives the actual point and Fourier window together. -/
lemma namedMeasuredMiddle_point_read (parameters : Parameters ctx) (index : WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment)
    {width : Nat} (observed : CStorageRef ctx (.ellipticCurvePoint width)) :
    NamedMiddlePreservesRead parameters index environment observed := by
  apply namedMeasuredMiddle_read_of_point
  · exact namedDriverInstrument_point_read (parameters.pointParameters index)
      parameters.frame parameters.modulus index.row environment observed
  · exact fun _ => write_shape_key_ne _ observed (by intro impossible; cases impossible)

end

end Locality

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
