/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Placement
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Horner.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Inverse.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Accumulate.Square.Program
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Controlled.Program

/-!
# Actual native arithmetic on the original point frame

Only static original port assignments and C/N selector identities select
syntax. Runtime operands remain quantum. Every full generated Horner/MAC
body is placed without unfolding its symbolic stage generator. Source
doubling, complete inverse restoration and both square-copy directions
remain the same paid native programs.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native

noncomputable section

open QuantumAlg.EncodedBit

/-- W remains workspace; the actual point selectors are precisely C and N. -/
inductive Control where
  | supplied
  | normal
deriving DecidableEq

/-- The restored original source can also supply the Horner multiplier bits. -/
inductive Multiplier where
  | source
  | retained
deriving DecidableEq

abbrev Circuit := UnitaryCircuit AlgorithmGate.model .empty
  (QubitLayout.canonical Frame.encoding.width).toQuantum

def controlBit (ports : PortAssignment) : Control → EncodedBit (Placement.restEncoding ports)
  | .supplied => Placement.savedPointControl ports
  | .normal => Placement.savedNormal ports

def outerBit (ports : PortAssignment) (control : Control) :
    EncodedBit (Placement.savedEncoding ports) :=
  Accumulate.Square.outerBit (Placement.restEncoding ports) (controlBit ports control)

def quantumMultiplier (ports : PortAssignment) :
    Multiplier → Horner.QuantumMultiplier (Placement.savedEncoding ports)
  | .source => Horner.QuantumMultiplier.source (Placement.savedEncoding ports)
  | .retained => Horner.QuantumMultiplier.retained (Placement.savedEncoding ports) Prod.fst
      (Accumulate.Square.multiplier (Placement.restEncoding ports)).bits
      (Accumulate.Square.multiplier (Placement.restEncoding ports)).reads

private lemma outer_source_ne (ports : PortAssignment) (control : Control) (index : Fin width) :
    (Horner.operandSavedBit (Placement.savedEncoding ports) (outerBit ports control)).wire ≠
      (Horner.operandSourceBit (Placement.savedEncoding ports) index).wire :=
  GateSpec.prodRightBit_wire_ne_prodLeftBit_wire ModularAddition.Controlled.selectorEncoding
    (Placement.savedEncoding ports) (outerBit ports control)
    (BinaryLabelEncoding.prodLeftBit ModularAddition.encoding
      ModularAddition.Controlled.flagEncoding (ModularAddition.addendBit index))

lemma outer_multiplier_ne (ports : PortAssignment) (control : Control)
    (multiplier : Multiplier) (index : Fin width) :
    (Horner.operandSavedBit (Placement.savedEncoding ports) (outerBit ports control)).wire ≠
      (Horner.operandMultiplierBit (Placement.savedEncoding ports)
        ((quantumMultiplier ports multiplier).ports index)).wire := by
  cases multiplier with
  | source => exact outer_source_ne ports control index
  | retained =>
    exact Accumulate.Square.outer_multiplier_ne
      (Placement.restEncoding ports) (controlBit ports control) index

/-- Actual complete clean-target multiplication on the original physical point words and pool. -/
def cleanProgram (ports : PortAssignment) (control : Control) (multiplier : Multiplier) : Circuit :=
  (Placement.layout ports).place
    (Horner.cleanProgram (Placement.savedEncoding ports) (quantumMultiplier ports multiplier)
      (outerBit ports control) (outer_multiplier_ne ports control multiplier))

/-- Actual arbitrary-accumulator MAC retains its independent original multiplier word. -/
def macProgram (ports : PortAssignment) (control : Control) : Circuit :=
  (Placement.layout ports).place
    (Accumulate.program (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control)))

/-- The entire same MAC's literal native adjoint acts on the same original physical positions. -/
def inverseMacProgram (ports : PortAssignment) (control : Control) : Circuit :=
  (Placement.layout ports).place
    (Accumulate.Inverse.program (Placement.savedEncoding ports)
      (Accumulate.Square.multiplier (Placement.restEncoding ports)) (outerBit ports control)
      (Accumulate.Square.outer_multiplier_ne
        (Placement.restEncoding ports) (controlBit ports control)))

/-- The original Y is squared into arbitrary X using the original genuinely clean A copy word. -/
def squarePorts : PortAssignment where
  source := .numerator
  target := .work2
  multiplier := .work1
  source_target := by decide
  source_multiplier := by decide
  target_multiplier := by decide

/-- Paid original Y-to-A XOR, full native inverse MAC, and full original A cleanup. -/
def subtractSquareProgram (control : Control) : Circuit :=
  (Placement.layout squarePorts).place
    (Accumulate.Square.program (Placement.restEncoding squarePorts)
      (controlBit squarePorts control))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Native
