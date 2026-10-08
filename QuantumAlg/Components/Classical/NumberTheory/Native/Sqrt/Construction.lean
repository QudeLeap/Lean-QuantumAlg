/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.Native.Sqrt.Layout
import all QuantumAlg.Components.Classical.ConstantWord.Circuit

/-!
# Actual native square-root construction with its own lexical scratch

The original input is widened into a fresh cell before any result is written.
A literal word loader supplies the first binary increment; the root comes
from its actual fresh-zero cell. Exactly the original input width's rounds
then refine the root, which is copied to the original destination. All six
scratch heads are released by the matching workspace instructions.

The zero-width word follows the same construction with no refinement round.
Original input and result storage may coincide because the source is saved
before the final copy. No existing quantum system is prepared or reset here.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Compilation-time first increment, with the empty-word case made explicit. -/
def initialHalf (width : Nat) : Nat :=
  if width = 0 then 0 else 2 ^ (width - 1)

/-- The complete original input is actually copied into its own twice-width cell. -/
def widenOp (input : CInputRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord (width + width))
      (context ctx width) (context ctx width) :=
  .wordResize width (width + width) (context ctx width)
    (underRead input width) (wideCell ctx width)

/-- Final copy to the actual original destination, under the six lexical heads. -/
def finishOp (output : CWriteRef ctx (.unsignedWord width)) :
    ClassicalOp (.unsignedWord width) (.unsignedWord width)
      (context ctx width) (context ctx width) :=
  .wordUnary .copy width (context ctx width)
    (.storage (rootCell ctx width).toCStorageRef) (underWrite output width)

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- Fixed-count execution of the same actual refinement round on its generated references. -/
def rounds (ctx : RuntimeCtx model.kind) (width : Nat) :
    Circuit model (context ctx width) (context ctx width) :=
  .iterate width
    (round (model := model) (.storage (wideCell ctx width).toCStorageRef) (roundRefs ctx width))

/-- Actual widening, literal increment load, fixed-count refinement and result copy. -/
def body (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) :
    Circuit model (context ctx width) (context ctx width) :=
  .seq (BitWord.instruction (execution := model) (widenOp input))
    (.seq (ConstantWord.circuit (model := model) (halfCell ctx width) (initialHalf width))
      (.seq (rounds (model := model) ctx width) (BitWord.instruction (execution := model)
        (finishOp output))))

/-- The real square-root program owns and releases every scratch cell it requires. -/
def into (input : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (.unsignedWord (width + width))
    ctx.canonicalFreshKey_fresh
    (.workspace (wideContext ctx width) (wideContext ctx width).canonicalFreshKey
      (.unsignedWord width) (wideContext ctx width).canonicalFreshKey_fresh
      (.workspace (rootContext ctx width) (rootContext ctx width).canonicalFreshKey
        (.unsignedWord width) (rootContext ctx width).canonicalFreshKey_fresh
        (.workspace (halfContext ctx width) (halfContext ctx width).canonicalFreshKey
          (.unsignedWord width) (halfContext ctx width).canonicalFreshKey_fresh
          (.workspace (candidateContext ctx width) (candidateContext ctx width).canonicalFreshKey
            (.unsignedWord (width + width)) (candidateContext ctx width).canonicalFreshKey_fresh
            (.workspace (squareContext ctx width) (squareContext ctx width).canonicalFreshKey
              .bit (squareContext ctx width).canonicalFreshKey_fresh (body (model := model) input
                output))))))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.NativeSqrt
