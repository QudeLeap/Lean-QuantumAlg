/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Program

/-!
# Actual per-window table lifetimes in the two-stream three-round schedule

The six calls are inside each individual table lifetime. The enclosing
point-arithmetic program can consume the same literal placement interface;
this file constructs only table preparation and load/unlookup fragments.
It does not reorder the old query-only schedule or identify this fragment
with complete point arithmetic.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

local notation "Model" =>
  ExecutionModel.quantum AlgorithmGate.model OracleModel.empty BitWord.model services

/-- The original two seventeen-row families are read at their actual untruncated indices. -/
def baseRow (stream : Fin 2) (window : Fin 17) : Fin 34 :=
  if stream.val = 0 then firstBaseRows window else secondBaseRows window

/-- One actual round prepares both base families, then builds/releases every individual table. -/
def roundCircuit (spec : ModulusSpec 256) (coefficient : Nat)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord 256))
    (column : Fin 6 → Fin 5) (round : Fin 3)
    (full : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      Fin 3 → Fin 2 → Fin 16 → Fin 6 → QueryPlacement encoding inner 256 8 7)
    (tail : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      Fin 3 → Fin 2 → Fin 6 → QueryPlacement encoding inner 256 2 1) :
    Circuit Model ctx ctx :=
  withCells (model := Model) ctx (sharedShapes 256) fun cells distinct lift _ =>
    let frame := Frame.ofCells cells distinct
    .seq (frame.initializeConstants spec coefficient)
      (.seq (frame.preparePairedBases spec
          (lift.liftInput firstX) (lift.liftInput firstY)
          (lift.liftInput secondX) (lift.liftInput secondY))
        (Circuit.forRange 2 fun stream =>
          .seq
            (Circuit.forRange 16 fun window =>
              frame.windowCircuit spec (baseRow stream window.castSucc) column
                (fun inside occurrence =>
                  full (lift.compose inside) round stream window occurrence))
            (frame.windowCircuit spec (baseRow stream ⟨16, by decide⟩) column
              (fun inside occurrence => tail (lift.compose inside) round stream occurrence))))

/-- Three actual rounds retain all paid base preparations, window builds and six physical calls. -/
def threeRoundCircuit (spec : ModulusSpec 256) (coefficient : Nat)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord 256))
    (column : Fin 6 → Fin 5)
    (full : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      Fin 3 → Fin 2 → Fin 16 → Fin 6 → QueryPlacement encoding inner 256 8 7)
    (tail : ∀ {inner : RuntimeCtx .quantum}, Transport ctx inner →
      Fin 3 → Fin 2 → Fin 6 → QueryPlacement encoding inner 256 2 1) :
    Circuit Model ctx ctx :=
  Circuit.forRange 3 fun round =>
    roundCircuit spec coefficient firstX firstY secondX secondY column round full tail

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
