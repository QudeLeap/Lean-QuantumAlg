/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame
import Mathlib.Data.List.FinRange

/-!
# The four original persistent scalar words

The finite family names product, inverse, temporary and slope in their
original physical order. Its injective storage keys are exactly the
separation already required by the actual frame.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Work

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- The original four scalar storage references in physical frame order. -/
def word (work : Work ctx width) : Fin 4 → CWriteRef ctx (.unsignedWord width) :=
  ![work.product, work.inverse, work.temporary, work.slope]

/-- Original physical separation makes the finite working-word keys injective. -/
lemma word_keys_injective (work : Work ctx width) :
    Function.Injective (fun index => (work.word index).key) := by
  apply List.nodup_ofFn.mp
  simpa [word, List.ofFn_succ] using work.distinct

/-- Different original working words have different actual storage keys. -/
lemma word_key_ne (work : Work ctx width) (first second : Fin 4)
    (different : first ≠ second) : (work.word first).key ≠ (work.word second).key :=
  fun same => different (work.word_keys_injective same)

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Work
