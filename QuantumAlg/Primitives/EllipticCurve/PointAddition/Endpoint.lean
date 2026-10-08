/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.EllipticCurve.PointAddition.Mathematics
public import QuantumAlg.Core.Base
public import QuantumAlg.Core.Base.Layout.Qubit
public import QuantumAlg.Core.Base.UnitaryCircuit.Binary.Width
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Primitives.EllipticCurve.Arithmetic.VariableModularMultiplication
public import QuantumAlg.Primitives.EllipticCurve.PointAddition.Basic
public import QuantumAlg.Primitives.EllipticCurve.PointAddition.ClosedForms
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.ClosedForms
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.ExceptionalCleanup
public import QuantumAlg.Util.EllipticCurve
public import Mathlib.Data.Nat.Log

/-!
# Public controlled elliptic-curve point-addition endpoint

This module exposes the literal clean controlled affine translation at the
published generic boundary.  The fixed addend is classical, the input point is
distinct from that addend and its inverse, and every auxiliary register is
restored.  Resource bounds are uniform functions of the field width.
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ControlledPointAddition

noncomputable section

variable [params : Arithmetic.VariableModularMul.Parameters]

variable {E : PrimeFieldShortWeierstrass params.modulus.val}

omit params in
private theorem translationToffoliBoundFor_eq_closed (fieldWidth : Nat) :
    GenericPointAddition.ExceptionalCleanup.translationToffoliBoundFor fieldWidth =
      toffoliCountBound fieldWidth := by
  rfl

omit params in
private theorem translationGateLengthBoundFor_eq_closed (fieldWidth : Nat) :
    GenericPointAddition.ExceptionalCleanup.translationGateLengthBoundFor fieldWidth =
      circuitDepthBound fieldWidth := by
  rfl

/-- Canonical production circuit for addition by the fixed classical point. -/
def program (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical
        GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width).toQuantum :=
  GenericPointAddition.ExceptionalCleanup.translationProgram (E := E) (Q := Q)

/-- Clean public boundary: one control, one mutable affine point, and zeroed
constant/output/work storage. -/
def cleanBoundary (control : Bool) (P : AffinePoint E) :
    GenericPointAddition.ExceptionalCleanup.Layout.RawRegisters :=
  GenericPointAddition.ExceptionalCleanup.Layout.translationBoundaryRegisters
    control (GenericPointAddition.Pipeline.pointWords P)
    (PointAddition.PortFrame.zeroPoint params.width)
    (PointAddition.PortFrame.zeroPoint params.width)

/-- The affine result selected by one control bit at the locked generic
boundary. -/
public def controlledResultPoint (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) (control : Bool)
    (P : AffinePoint E) (hPQ : P ≠ Q)
    (hPnegQ : P ≠ AffinePoint.negate Q) : AffinePoint E :=
  if control then
    GenericPointAddition.Pipeline.resultPoint
      (⟨P, genericAddDomain_of_ne_of_ne_negate E P Q hPQ hPnegQ⟩ :
        GenericPointAddition.Input E Q)
  else P

/-- The selected finite result is exactly addition by the bit-selected fixed
point in Mathlib's affine group. -/
theorem controlledResultPoint_group_law
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) (control : Bool)
    (P : AffinePoint E) (hPQ : P ≠ Q)
    (hPnegQ : P ≠ AffinePoint.negate Q) :
    (controlledResultPoint E Q control P hPQ hPnegQ).toMathlib =
      P.toMathlib + if control then Q.toMathlib else 0 := by
  let input : GenericPointAddition.Input E Q :=
    ⟨P, genericAddDomain_of_ne_of_ne_negate E P Q hPQ hPnegQ⟩
  cases control with
  | false => simp [controlledResultPoint]
  | true =>
      simpa only [controlledResultPoint, Bool.true_eq, ↓reduceIte, input] using
        (GenericPointAddition.Pipeline.resultPoint_group_law_mathlib
          input).symm

/-- The canonical program occupies exactly its named width-indexed logical
carrier. -/
theorem program_width_exact :
    GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding.width =
      logicalQubitCount params.width := by
  rw [GenericPointAddition.ExceptionalCleanup.Layout.rawEncoding_width_exact]
  simp only [logicalQubitCount, Arithmetic.ModularInversion.physicalWidthFor,
    Arithmetic.ModularInversion.counterWidthFor]
  omega

/-- Clean computational-basis state on the fixed public-width carrier.  The
private arithmetic and selector fields are initialized to their canonical
zero values inside this constructor. -/
public def cleanState (control : Bool) (P : AffinePoint E) :
    NormalizedVector
      (QubitLayout.canonical (logicalQubitCount params.width)).toQuantum.register :=
  (program_width_exact (params := params)) ▸
    GenericPointAddition.ExceptionalCleanup.encodedKet (cleanBoundary control P)

/-- The literal implementation regrouped to its public logical width. -/
private def publicProgram
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (logicalQubitCount params.width)).toQuantum :=
  (program E Q).castCanonicalQubitWidth (program_width_exact (params := params))

/-- Same-circuit Toffoli projection, bounded by the closed width family. -/
theorem program_toffoli_count_le
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program E Q).eventCost ≤ toffoliCountBound params.width := by
  rw [← translationToffoliBoundFor_eq_closed params.width]
  simpa only [program,
    GenericPointAddition.ExceptionalCleanup.translationToffoliBound] using
    (GenericPointAddition.ExceptionalCleanup.translationProgram_toffoli_count_le
      (E := E) (Q := Q))

/-- The same actual program obeys the normalized polynomial bound used by the
public statement. -/
theorem program_toffoli_count_le_published
    (hcharacteristic : 3 < params.modulus.val)
    (hfieldWidth : params.width = Nat.clog 2 params.modulus.val)
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program E Q).eventCost ≤
      publishedToffoliCountBound (Nat.clog 2 params.modulus.val) := by
  have fieldWidthPositive : 0 < Nat.clog 2 params.modulus.val :=
    Nat.clog_pos (by norm_num) (by omega)
  have fieldWidthGreaterThanOne : 1 < Nat.clog 2 params.modulus.val :=
    (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by norm_num; omega)
  have heightAtLeastTwo :
      2 ≤ Nat.clog 2 (2 * Nat.clog 2 params.modulus.val) := by
    have logarithmGreaterThanOne :
        1 < Nat.clog 2 (2 * Nat.clog 2 params.modulus.val) :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).2 (by norm_num; omega)
    omega
  calc
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program E Q).eventCost ≤ toffoliCountBound params.width :=
      program_toffoli_count_le E Q
    _ = publishedToffoliCountBound (Nat.clog 2 params.modulus.val) :=
      (congrArg toffoliCountBound hfieldWidth).trans
        (toffoliCountBound_eq_published _ fieldWidthPositive heightAtLeastTwo)

/-- Same-circuit sequential unit-depth projection, bounded by the closed width
family. -/
theorem program_unitDepth_le
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) :
    (program E Q).evaluatedEventDepth (fun _ => 1) ≤
      circuitDepthBound params.width := by
  rw [← translationGateLengthBoundFor_eq_closed params.width]
  simpa only [program,
    GenericPointAddition.ExceptionalCleanup.translationGateLengthBound] using
    (GenericPointAddition.ExceptionalCleanup.translationProgram_unitDepth_le
      (E := E) (Q := Q))

/-- Basis-state action of the canonical circuit at the locked generic
boundary, with every auxiliary field restored. -/
theorem program_clean_ket
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) (control : Bool)
    (P : AffinePoint E) (hPQ : P ≠ Q)
    (hPnegQ : P ≠ AffinePoint.negate Q) :
    (program E Q).applyNormalized
        (GenericPointAddition.ExceptionalCleanup.encodedKet
          (cleanBoundary control P)) =
      GenericPointAddition.ExceptionalCleanup.encodedKet
        (cleanBoundary control
          (controlledResultPoint E Q control P hPQ hPnegQ)) := by
  let input : GenericPointAddition.Input E Q :=
    ⟨P, genericAddDomain_of_ne_of_ne_negate E P Q hPQ hPnegQ⟩
  have h :=
    GenericPointAddition.ExceptionalCleanup.translationProgram_clean_ket
      (E := E) (Q := Q) control input
  cases control with
  | false =>
      simpa [program, cleanBoundary, controlledResultPoint, input,
        GenericPointAddition.Pipeline.resultWords] using h
  | true =>
      simpa [program, cleanBoundary, controlledResultPoint, input,
        GenericPointAddition.Pipeline.resultWords] using h

/-- The public-width regrouping retains the exact clean controlled action. -/
theorem publicProgram_clean_ket
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) (control : Bool)
    (P : AffinePoint E) (hPQ : P ≠ Q)
    (hPnegQ : P ≠ AffinePoint.negate Q) :
    (publicProgram E Q).applyNormalized (cleanState control P) =
      cleanState control (controlledResultPoint E Q control P hPQ hPnegQ) := by
  let same := program_width_exact (params := params)
  let input := GenericPointAddition.ExceptionalCleanup.encodedKet (cleanBoundary control P)
  let output := GenericPointAddition.ExceptionalCleanup.encodedKet
    (cleanBoundary control (controlledResultPoint E Q control P hPQ hPnegQ))
  have action : (program E Q).applyNormalized input = output := by
    simpa [input, output] using
      program_clean_ket E Q control P hPQ hPnegQ
  calc
    (publicProgram E Q).applyNormalized (cleanState control P) =
        same ▸ (program E Q).applyNormalized input := by
      simpa [publicProgram, cleanState, same, input] using
        UnitaryCircuit.castCanonicalQubitWidth_applyNormalized same (program E Q) input
    _ = same ▸ output := congrArg (fun state => same ▸ state) action
    _ = cleanState control
        (controlledResultPoint E Q control P hPQ hPnegQ) := by
      rfl

/-- A false control leaves every clean affine input unchanged, including the
two inputs excluded from the active generic-addition domain. -/
theorem program_clean_ket_of_control_false
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q P : AffinePoint E) :
    (program E Q).applyNormalized
        (GenericPointAddition.ExceptionalCleanup.encodedKet
          (cleanBoundary false P)) =
      GenericPointAddition.ExceptionalCleanup.encodedKet
        (cleanBoundary false P) := by
  have action :=
    (GenericPointAddition.ExceptionalCleanup.translationProgram_realizes
      (E := E) (Q := Q)).apply_encoded_ket (cleanBoundary false P)
  have unchanged :=
    GenericPointAddition.ExceptionalCleanup.translationStep_eq_self_of_control_false
      (E := E) (Q := Q) (cleanBoundary false P) (by rfl)
  rw [unchanged] at action
  simpa only [program, cleanBoundary,
    GenericPointAddition.ExceptionalCleanup.encodedKet] using action

/-- **Elliptic-curve point addition.**  For a prime characteristic above three
and its canonical binary field width, the same literal circuit has the exact
logical and auxiliary widths, the published Toffoli and existing sequential
depth bounds, and the controlled in-place group-shift action for every affine
input distinct from the fixed addend and its inverse. -/
public theorem main (hcharacteristic : 3 < params.modulus.val)
    (hfieldWidth : params.width = Nat.clog 2 params.modulus.val)
    (E : PrimeFieldShortWeierstrass params.modulus.val)
    [Fact params.modulus.val.Prime] (Q : AffinePoint E) :
    ∃ circuit : UnitaryCircuit AlgorithmGate.model .empty
        (QubitLayout.canonical (logicalQubitCount params.width)).toQuantum,
      logicalQubitCount (Nat.clog 2 params.modulus.val) =
          (1 + 2 * Nat.clog 2 params.modulus.val) +
            auxiliaryQubitCount (Nat.clog 2 params.modulus.val) ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
          circuit.eventCost ≤
        publishedToffoliCountBound (Nat.clog 2 params.modulus.val) ∧
      circuit.evaluatedEventDepth (fun _ => 1) ≤
        circuitDepthBound (Nat.clog 2 params.modulus.val) ∧
      ∀ (control : Bool) (P : AffinePoint E)
        (hPQ : P ≠ Q) (hPnegQ : P ≠ AffinePoint.negate Q),
        circuit.applyNormalized
            (cleanState control P) =
          cleanState control
            (controlledResultPoint E Q control P hPQ hPnegQ) ∧
        (controlledResultPoint E Q control P hPQ hPnegQ).toMathlib =
          P.toMathlib + if control then Q.toMathlib else 0 := by
  refine ⟨publicProgram E Q,
    logicalQubitCount_eq_public_add_auxiliary _, ?_, ?_, ?_⟩
  · rw [publicProgram, UnitaryCircuit.castCanonicalQubitWidth_eventCost]
    exact program_toffoli_count_le_published hcharacteristic hfieldWidth E Q
  · rw [publicProgram, UnitaryCircuit.castCanonicalQubitWidth_evaluatedEventDepth]
    simpa [hfieldWidth] using program_unitDepth_le E Q
  · intro control P hPQ hPnegQ
    exact ⟨publicProgram_clean_ket E Q control P hPQ hPnegQ,
      controlledResultPoint_group_law E Q control P hPQ hPnegQ⟩

end

end ControlledPointAddition
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
