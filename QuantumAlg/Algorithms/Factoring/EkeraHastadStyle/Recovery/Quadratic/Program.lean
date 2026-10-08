/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.LocalSelection.Layout
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.Recovery.Quadratic.Selection.Narrow

/-!
# Actual scoped quadratic recovery and persistent factor selection

The circuit materializes both original quadratic candidates, loads the one
operand with two real instructions, performs both complete divisor checks,
and chooses the first valid wide candidate in local latches. A real scoped
width conversion then supplies the persistent selector, which preserves any
earlier accepted factor. All temporary cells are released in reverse scope
order. The same original quantum bank remains present throughout.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic

open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
  {width resultWidth : Nat}

/-- Both complete checks and local selection precede the actual persistent result update. -/
def checkedBody (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) :
    Circuit model (LocalLayout.context ctx width) (LocalLayout.context ctx width) :=
  let pair := LocalLayout.pairRefs modulus
  .seq (Pair.code pair)
    (NarrowSelection.code (FirstAccepted.cellRead pair.selection.accepted)
      (FirstAccepted.cellRead pair.selection.selected) (LocalLayout.persistentRefs original width))

/-- Actual candidate arithmetic and constant loading precede the five real checker scopes. -/
def candidateBody (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) :
    Circuit model (LocalLayout.candidateContext ctx width)
      (LocalLayout.candidateContext ctx width) :=
  .seq (Initialized.code (LocalLayout.arithmeticRead input width)
    (LocalLayout.arithmeticRead modulus width) (LocalLayout.arithmeticRefs ctx width))
    (CheckLayout.scopes (LocalLayout.candidateContext ctx width) (RSA.quadraticWordWidth width)
      (checkedBody modulus original))

/-- Complete actual quadratic recovery uses only scoped classical work and the original latches.
-/
def program (input : CInputRef ctx (.unsignedWord width))
    (modulus : CInputRef ctx (.unsignedWord (RSA.quadraticWordWidth width)))
    (original : FirstAccepted.Refs ctx resultWidth) : Circuit model ctx ctx :=
  SelectionLayout.scopes ctx (RSA.quadraticWordWidth width)
    (Layout.scopes (LocalLayout.selectionContext ctx width) width
      (candidateBody input modulus original))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeRecovery.Quadratic
