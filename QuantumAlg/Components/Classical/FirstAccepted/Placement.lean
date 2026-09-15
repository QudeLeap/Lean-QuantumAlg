/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.FirstAccepted.Circuit
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate

/-!
# Original first-accepted selection with actual lexical scratch

The original availability bit is allocated before the inner take bit. The
existing selector executes its negation, conjunction and stored copy branch
with the original persistent latches. Both scratch cells are released before
returning to the same caller context, allowing every attempt to reuse them.
-/

namespace QuantumAlg.ClassicalRoutines.FirstAccepted

open Execution ClassicalWorkspace

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Structural placement retains both original selector inputs. -/
def placedInputs {inner : RuntimeCtx kind} (inputs : Inputs ctx width)
    (transport : Transport ctx inner) : Inputs inner width :=
  ⟨transport.liftInput inputs.eligible, transport.liftInput inputs.candidate⟩

/-- The original inner take and outer availability cells accompany both persistent latches. -/
def placedRefs {inner : RuntimeCtx kind} (cells : Cells inner [.bit, .bit])
    (transport : Transport ctx inner) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width)) : Refs inner width :=
  ⟨transport.liftWrite accepted, transport.liftWrite selected,
    cells.tail.head.ref, cells.head.ref⟩

/-- Allocate the original two bits, run the original stored selector, and release both bits. -/
def withSelection (inputs : Inputs ctx width) (accepted : CWriteRef ctx .bit)
    (selected : CWriteRef ctx (.unsignedWord width)) : Circuit ctx ctx :=
  withCells ctx [.bit, .bit] fun cells _ transport _ =>
    circuit (placedInputs inputs transport) (placedRefs cells transport accepted selected)

end QuantumAlg.ClassicalRoutines.FirstAccepted
