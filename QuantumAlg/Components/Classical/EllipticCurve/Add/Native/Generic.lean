/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Add.Native.Affine.Semantics

/-!
# Actual original generic finite addition arm

The original two field subtractions materialize the numerator and denominator
in two actual lexical cells. The same original total affine tail consumes
those results. No table, inverse witness or caller workspace is an input.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original numerator then denominator allocation, represented deepest first. -/
def genericShapes (width : Nat) : List CShape := [.unsignedWord width, .unsignedWord width]

/-- The two original subtractions precede the shared original affine tail. -/
def genericBody (spec : ModulusSpec width)
    (leftX leftY rightX rightY : CInputRef ctx (.unsignedWord width))
    (numerator denominator : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) : Circuit ctx ctx :=
  .seq (Field.Native.subIntoWord spec rightY leftY numerator)
    (.seq (Field.Native.subIntoWord spec rightX leftX denominator)
      (affineInto spec leftX rightX leftY (classifierRead numerator) (classifierRead denominator)
        output))

/-- The native record threads the real intermediate stores through both subtractions and tail. -/
def genericBodyStep (spec : ModulusSpec width)
    (leftX leftY rightX rightY : CInputRef ctx (.unsignedWord width))
    (numerator denominator : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) :
    Store ctx → Store ctx × (genericBody spec leftX leftY rightX rightY numerator denominator
      output).Path :=
  Circuit.sequenceRecord _ _ (Field.Native.subIntoWordStep spec rightY leftY numerator)
    (Circuit.sequenceRecord _ _ (Field.Native.subIntoWordStep spec rightX leftX denominator)
      (affineIntoStep spec leftX rightX leftY (classifierRead numerator)
        (classifierRead denominator)
        output))

/-- The actual generic arm retains all complete quantum-reference blocks and original history. -/
theorem genericBody_execute (spec : ModulusSpec width)
    (leftX leftY rightX rightY : CInputRef ctx (.unsignedWord width))
    (numerator denominator : CWriteRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (PointShape width)) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (genericBody spec leftX leftY rightX rightY numerator denominator output).execute
      Reference state = state.mapClassical (fun entry =>
        ((genericBodyStep spec leftX leftY rightX rightY numerator denominator output entry.1).1,
          (entry.2, (genericBodyStep spec leftX leftY rightX rightY numerator denominator output
            entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _ (Field.Native.subIntoWord_execute _ _ _ _)
    (Circuit.execute_sequenceRecord _ _ _ _ (Field.Native.subIntoWord_execute _ _ _ _)
      (affineInto_execute _ _ _ _ _ _ _)) Reference state

/-- Actual lexical allocation supplies both original prefix cells, with no caller promises. -/
def genericInto (spec : ModulusSpec width)
    (left right : CInputRef ctx (PointEquality.RawPointShape width))
    (output : CWriteRef ctx (PointShape width)) : Circuit ctx ctx :=
  withCells ctx (genericShapes width) fun cells _ transport _ =>
    let leftAt := transport.liftInput left
    let rightAt := transport.liftInput right
    genericBody spec (.first (.second leftAt)) (.second (.second leftAt))
      (.first (.second rightAt)) (.second (.second rightAt)) cells.tail.head.ref cells.head.ref
      (transport.liftWrite output)

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.Add.Native
