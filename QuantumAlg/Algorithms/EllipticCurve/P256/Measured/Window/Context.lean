/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.Context
public import QuantumAlg.Core.Base.Accounting.Shape
public import QuantumAlg.Algorithms.EllipticCurve.P256.DomainParameters
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.PublicInput
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Run

/-!
# Public contexts of the paid P-256 window execution

The input is the unchanged borrowed two-point frame. The final context retains
the actual allocated bank, measurement and table cells and packed optional word.
These contexts and output shape specify the interface independently of success.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window

noncomputable section

open ClassicalRoutines.EllipticCurve

/-- The original borrowed public points, before any bank or table allocation. -/
public def Pre (I : DomainParameters.PublicKeyInstance) : RuntimeCtx .quantum :=
  Factory.publicFrame I

/-- The actual retained bank, classical cells and paid optional-result destination. -/
public def Post (I : DomainParameters.PublicKeyInstance) : RuntimeCtx .quantum :=
  CandidateCheck.Native.batchResultCtx
    (Factory.tableContext (Factory.publicFrame I) (Factory.publicFrame_noQuantum I)) 256 260

/-- The literal optional 260-bit scalar returned by the final native pack. -/
public def OutputShape : CShape := .option (.unsignedWord 260)

/-- Every admitted public frame has no caller quantum bank. -/
lemma pre_noQuantum (I : DomainParameters.PublicKeyInstance) :
    (Pre I).quantumWires = [] :=
  Factory.publicFrame_noQuantum I

end

end QuantumAlg.EllipticCurve.P256.Measured.Window
