/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Parameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.FullRange.Seed.Chronological
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Resources.Modulus
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Parameters
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Recovery.Transport

/-!
# One literal P-256 field configuration beside the original sampling ports

The curve is bound once and supplies the same modulus specification to the
actual table sampler. Original wires, Fourier results, the complete shared
frame and nominal point references are retained. The order specification uses
the generic known-order construction, and both seed words are coordinates of
the same chronological fixed seed.

This only constructs internal parameters. It neither changes arbitrary
storage inputs nor prepares their classical values, allocates a physical
bank, executes a sampler or proves a success probability.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

namespace Factory

noncomputable section

open Execution ClassicalWorkspace PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open ClassicalAlgorithms.Modular
open ClassicalRoutines.EllipticCurve

private def fitModulusSpec {first last : Nat} (same : first = last)
    (spec : ModulusSpec first) : ModulusSpec last where
  modulus := spec.modulus
  two_le := spec.two_le
  le_capacity := by
    cases same
    exact spec.le_capacity

private lemma fitModulusSpec_eq_cast {first last : Nat} (same : first = last)
    (spec : ModulusSpec first) :
    fitModulusSpec same spec = (same ▸ spec : ModulusSpec last) := by
  cases same
  cases spec
  rfl

private def orderSpec (I : DomainParameters.PublicKeyInstance) : ModulusSpec 260 :=
  fitModulusSpec (first := Cascade.exponentWidth I) (last := 260)
    (Cascade.exponentWidth_eq_260 I)
    (FiniteCyclicDLP.Canonical.resourceModulusSpec
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I)) I.subgroupCert.prime.two_le :
        ModulusSpec (Cascade.exponentWidth I))

private lemma orderSpec_modulus (I : DomainParameters.PublicKeyInstance) :
    (orderSpec I).modulus = DomainParameters.subgroupOrder := rfl

private def seedWords (I : DomainParameters.PublicKeyInstance) :
    Fin (2 ^ 256) × Fin (2 ^ 256) :=
  let curve := actualCurveSpec I
  let seed := FullRange.chronologicalFixedSeed I
  (ClassicalAlgorithms.EllipticCurve.coordinateWord curve seed.x,
    ClassicalAlgorithms.EllipticCurve.coordinateWord curve seed.y)

variable {ctx : RuntimeCtx .quantum} (I : DomainParameters.PublicKeyInstance)
    (sameWires : (QubitLayout.canonical encoding.width).toQuantum.wires =
      ctx.quantumLayout.wires)
    (results : Fourier.Results ctx)
    (frame : ClassicalRoutines.EllipticCurve.WindowTables.Outer.Frame ctx 256)
    (base target : CInputRef ctx (PointShape 256))

/-- Original ports share one literal curve field and the same fixed chronological seed. -/
def inputs : Sampling.Storage.Inputs ctx :=
  let curve := actualCurveSpec I
  { sameWires := sameWires
    results := results
    frame := frame
    modulus := curve.field
    curve := curve
    order := orderSpec I
    base := base
    target := target
    seedX := (seedWords I).1
    seedY := (seedWords I).2 }

/-- The complete curve specification is the same original certified P-256 value. -/
lemma inputs_curve :
    (inputs I sameWires results frame base target).curve = actualCurveSpec I := rfl

/-- The executed sampler specification is the curve's actual field, not a stored-word claim. -/
lemma inputs_modulus :
    (inputs I sameWires results frame base target).modulus =
      (inputs I sameWires results frame base target).curve.field := rfl

/-- Every original port is retained, including all four constants and both complete arrays. -/
lemma inputs_original_ports :
    ((inputs I sameWires results frame base target).results,
      (inputs I sameWires results frame base target).frame,
      (inputs I sameWires results frame base target).base,
      (inputs I sameWires results frame base target).target) =
        (results, frame, base, target) := rfl

/-- The generic fitted order specification has the original subgroup modulus. -/
lemma inputs_order :
    (inputs I sameWires results frame base target).order.modulus =
      DomainParameters.subgroupOrder := orderSpec_modulus I

/-- Both actual loader words contain coordinates of the same chronological fixed seed. -/
lemma inputs_fixed_seed :
    ((inputs I sameWires results frame base target).seedX.val,
      (inputs I sameWires results frame base target).seedY.val) =
        ((FullRange.chronologicalFixedSeed I).x.val,
          (FullRange.chronologicalFixedSeed I).y.val) := rfl

variable {inner : RuntimeCtx .quantum} (lift : Transport ctx inner)
    (same : ctx.quantumLayout.wires = inner.quantumLayout.wires)

/-- Original structural transport retains the literal curve and modulus identity. -/
lemma transported_modulus :
    ((inputs I sameWires results frame base target).transport lift same).modulus =
      ((inputs I sameWires results frame base target).transport lift same).curve.field := rfl

/-- The actual scratch-backed sampler receives exactly the transported curve's field. -/
lemma sampler_modulus (scratch : Sampling.Storage.Frame inner 256 256)
    (fresh : Sampling.Storage.CallerFree scratch lift) :
    ((inputs I sameWires results frame base target).samplerParameters
      lift same scratch fresh).modulus =
        ((inputs I sameWires results frame base target).transport lift same).curve.field := rfl

/-- The real retained-checker and feedback transports keep the same program specification. -/
lemma retained_sampler_modulus
    (next : Transport
      (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx ctx 256 260) inner)
    (nextWires :
      (ClassicalRoutines.EllipticCurve.CandidateCheck.Native.persistentCtx
        ctx 256 260).quantumLayout.wires = inner.quantumLayout.wires)
    (scratch : Sampling.Storage.Frame inner 256 256)
    (fresh : Sampling.Storage.CallerFree scratch next) :
    let retained := (inputs I sameWires results frame base target).transport
      (Sampling.Recovery.persistentTransport ctx) (Sampling.Recovery.persistent_wires ctx)
    (retained.samplerParameters next nextWires scratch fresh).modulus =
      (retained.transport next nextWires).curve.field := rfl

end

end Factory

end QuantumAlg.EllipticCurve.P256.Measured.Window
