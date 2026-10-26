/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word28Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word28State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word28Step0 :
    word28Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word28State1 := by decide +kernel

private def word28Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word28State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word28Step1 :
    word28Chunk1.foldl (fun acc a => a.applyPacked acc)
      word28State1 = word28State2 := by decide +kernel

private def word28Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word28State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word28Step2 :
    word28Chunk2.foldl (fun acc a => a.applyPacked acc)
      word28State2 = word28State3 := by decide +kernel

private def word28Chunk3 : List Letter := [.s, .h, .s, .t, .h, .t, .h, .s]
private def word28State4 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word28Step3 :
    word28Chunk3.foldl (fun acc a => a.applyPacked acc)
      word28State3 = word28State4 := by decide +kernel

private def word28Chunk4 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word28State5 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-5 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word28Step4 :
    word28Chunk4.foldl (fun acc a => a.applyPacked acc)
      word28State4 = word28State5 := by decide +kernel

private def word28Chunk5 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word28State6 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word28Step5 :
    word28Chunk5.foldl (fun acc a => a.applyPacked acc)
      word28State5 = word28State6 := by decide +kernel

private def word28Chunk6 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word28State7 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((11 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word28Step6 :
    word28Chunk6.foldl (fun acc a => a.applyPacked acc)
      word28State6 = word28State7 := by decide +kernel

private def word28Chunk7 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word28State8 : PackedMat2 :=
    ⟨⟨⟨((23 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-11 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((7 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((17 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word28Step7 :
    word28Chunk7.foldl (fun acc a => a.applyPacked acc)
      word28State7 = word28State8 := by decide +kernel

private def word28Chunk8 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word28State9 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((27 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-31 : Dyadic) * half ^ 6)⟩,
       ⟨(0 : Dyadic),
        ((-23 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 6)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((11 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word28Step8 :
    word28Chunk8.foldl (fun acc a => a.applyPacked acc)
      word28State8 = word28State9 := by decide +kernel

private def word28Chunk9 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word28State10 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-47 : Dyadic) * half ^ 7)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 6),
        ((-41 : Dyadic) * half ^ 7)⟩,
       ⟨((33 : Dyadic) * half ^ 6),
        ((-17 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 6),
        ((41 : Dyadic) * half ^ 7)⟩,
       ⟨((33 : Dyadic) * half ^ 6),
        ((-17 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-47 : Dyadic) * half ^ 7)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((11 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word28Step9 :
    word28Chunk9.foldl (fun acc a => a.applyPacked acc)
      word28State9 = word28State10 := by decide +kernel

private def word28Chunk10 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word28State11 : PackedMat2 :=
    ⟨⟨⟨((-3 : Dyadic) * half ^ 3),
        ((31 : Dyadic) * half ^ 8)⟩,
       ⟨((-31 : Dyadic) * half ^ 7),
        ((-133 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-45 : Dyadic) * half ^ 7),
        ((59 : Dyadic) * half ^ 8)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((5 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 8)⟩,
       ⟨((45 : Dyadic) * half ^ 7),
        ((-59 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-31 : Dyadic) * half ^ 7),
        ((-133 : Dyadic) * half ^ 8)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((31 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word28Step10 :
    word28Chunk10.foldl (fun acc a => a.applyPacked acc)
      word28State10 = word28State11 := by decide +kernel

private def word28Chunk11 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word28State12 : PackedMat2 :=
    ⟨⟨⟨((33 : Dyadic) * half ^ 7),
        ((21 : Dyadic) * half ^ 8)⟩,
       ⟨((-113 : Dyadic) * half ^ 7),
        ((7 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((43 : Dyadic) * half ^ 7),
        ((19 : Dyadic) * half ^ 8)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((37 : Dyadic) * half ^ 8),
        ((47 : Dyadic) * half ^ 8)⟩,
       ⟨((1 : Dyadic) * half ^ 8),
        ((39 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-35 : Dyadic) * half ^ 8),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((-7 : Dyadic) * half ^ 8),
        ((-73 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word28Step11 :
    word28Chunk11.foldl (fun acc a => a.applyPacked acc)
      word28State11 = word28State12 := by decide +kernel

private def word28Chunk12 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word28State13 : PackedMat2 :=
    ⟨⟨⟨((89 : Dyadic) * half ^ 8),
        ((45 : Dyadic) * half ^ 7)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        ((79 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((29 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 8)⟩,
       ⟨((21 : Dyadic) * half ^ 6),
        ((-51 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-21 : Dyadic) * half ^ 6),
        ((51 : Dyadic) * half ^ 9)⟩,
       ⟨((-29 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((79 : Dyadic) * half ^ 9)⟩,
       ⟨((89 : Dyadic) * half ^ 8),
        ((45 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word28Step12 :
    word28Chunk12.foldl (fun acc a => a.applyPacked acc)
      word28State12 = word28State13 := by decide +kernel

private def word28Chunk13 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word28State14 : PackedMat2 :=
    ⟨⟨⟨((43 : Dyadic) * half ^ 9),
        ((405 : Dyadic) * half ^ 10)⟩,
       ⟨((-143 : Dyadic) * half ^ 9),
        ((379 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-35 : Dyadic) * half ^ 8),
        ((-355 : Dyadic) * half ^ 10)⟩,
       ⟨((-19 : Dyadic) * half ^ 7),
        ((-157 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-99 : Dyadic) * half ^ 9),
        ((3 : Dyadic) * half ^ 9)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((73 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 9),
        ((-93 : Dyadic) * half ^ 9)⟩,
       ⟨((49 : Dyadic) * half ^ 6),
        ((-25 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word28Step13 :
    word28Chunk13.foldl (fun acc a => a.applyPacked acc)
      word28State13 = word28State14 := by decide +kernel

private def word28Chunk14 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word28State15 : PackedMat2 :=
    ⟨⟨⟨((-589 : Dyadic) * half ^ 10),
        ((215 : Dyadic) * half ^ 11)⟩,
       ⟨((447 : Dyadic) * half ^ 10),
        ((153 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 5),
        ((-801 : Dyadic) * half ^ 11)⟩,
       ⟨((77 : Dyadic) * half ^ 8),
        ((-227 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 5),
        ((801 : Dyadic) * half ^ 11)⟩,
       ⟨((77 : Dyadic) * half ^ 8),
        ((-227 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-589 : Dyadic) * half ^ 10),
        ((215 : Dyadic) * half ^ 11)⟩,
       ⟨((-447 : Dyadic) * half ^ 10),
        ((-153 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word28Step14 :
    word28Chunk14.foldl (fun acc a => a.applyPacked acc)
      word28State14 = word28State15 := by decide +kernel

private def word28Chunk15 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word28State16 : PackedMat2 :=
    ⟨⟨⟨((141 : Dyadic) * half ^ 10),
        ((-1479 : Dyadic) * half ^ 12)⟩,
       ⟨((-149 : Dyadic) * half ^ 11),
        ((1577 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-925 : Dyadic) * half ^ 11),
        ((-235 : Dyadic) * half ^ 12)⟩,
       ⟨((-89 : Dyadic) * half ^ 9),
        ((-1221 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((89 : Dyadic) * half ^ 9),
        ((1221 : Dyadic) * half ^ 12)⟩,
       ⟨((925 : Dyadic) * half ^ 11),
        ((235 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-149 : Dyadic) * half ^ 11),
        ((1577 : Dyadic) * half ^ 12)⟩,
       ⟨((141 : Dyadic) * half ^ 10),
        ((-1479 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word28Step15 :
    word28Chunk15.foldl (fun acc a => a.applyPacked acc)
      word28State15 = word28State16 := by decide +kernel

private def word28Chunk16 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word28State17 : PackedMat2 :=
    ⟨⟨⟨((-999 : Dyadic) * half ^ 12),
        ((1713 : Dyadic) * half ^ 13)⟩,
       ⟨((-63 : Dyadic) * half ^ 9),
        ((2375 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((659 : Dyadic) * half ^ 11),
        ((-1041 : Dyadic) * half ^ 13)⟩,
       ⟨((-1085 : Dyadic) * half ^ 12),
        ((-3945 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-363 : Dyadic) * half ^ 10),
        ((-2403 : Dyadic) * half ^ 13)⟩,
       ⟨((-2493 : Dyadic) * half ^ 12),
        ((233 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-331 : Dyadic) * half ^ 12),
        ((-495 : Dyadic) * half ^ 13)⟩,
       ⟨((-511 : Dyadic) * half ^ 10),
        ((1503 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word28Step16 :
    word28Chunk16.foldl (fun acc a => a.applyPacked acc)
      word28State16 = word28State17 := by decide +kernel

private def word28Chunk17 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word28State18 : PackedMat2 :=
    ⟨⟨⟨((-35 : Dyadic) * half ^ 10),
        ((-3493 : Dyadic) * half ^ 13)⟩,
       ⟨((-59 : Dyadic) * half ^ 9),
        ((-483 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((111 : Dyadic) * half ^ 10),
        ((3447 : Dyadic) * half ^ 13)⟩,
       ⟨((-1067 : Dyadic) * half ^ 12),
        ((145 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((1067 : Dyadic) * half ^ 12),
        ((-145 : Dyadic) * half ^ 9)⟩,
       ⟨((-111 : Dyadic) * half ^ 10),
        ((-3447 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-59 : Dyadic) * half ^ 9),
        ((-483 : Dyadic) * half ^ 12)⟩,
       ⟨((-35 : Dyadic) * half ^ 10),
        ((-3493 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word28Step17 :
    word28Chunk17.foldl (fun acc a => a.applyPacked acc)
      word28State17 = word28State18 := by decide +kernel

private def word28Chunk18 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word28State19 : PackedMat2 :=
    ⟨⟨⟨((-4915 : Dyadic) * half ^ 14),
        ((2197 : Dyadic) * half ^ 14)⟩,
       ⟨((-7979 : Dyadic) * half ^ 14),
        ((-1907 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((11555 : Dyadic) * half ^ 14),
        ((-441 : Dyadic) * half ^ 12)⟩,
       ⟨((1069 : Dyadic) * half ^ 14),
        ((701 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((11555 : Dyadic) * half ^ 14),
        ((-441 : Dyadic) * half ^ 12)⟩,
       ⟨((-1069 : Dyadic) * half ^ 14),
        ((-701 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((4915 : Dyadic) * half ^ 14),
        ((-2197 : Dyadic) * half ^ 14)⟩,
       ⟨((-7979 : Dyadic) * half ^ 14),
        ((-1907 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word28Step18 :
    word28Chunk18.foldl (fun acc a => a.applyPacked acc)
      word28State18 = word28State19 := by decide +kernel

private def word28Chunk19 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word28State20 : PackedMat2 :=
    ⟨⟨⟨((2055 : Dyadic) * half ^ 12),
        ((1049 : Dyadic) * half ^ 12)⟩,
       ⟨((1255 : Dyadic) * half ^ 14),
        ((-1687 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-5275 : Dyadic) * half ^ 13),
        ((2387 : Dyadic) * half ^ 14)⟩,
       ⟨((3903 : Dyadic) * half ^ 14),
        ((-325 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((5275 : Dyadic) * half ^ 13),
        ((-2387 : Dyadic) * half ^ 14)⟩,
       ⟨((3903 : Dyadic) * half ^ 14),
        ((-325 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((2055 : Dyadic) * half ^ 12),
        ((1049 : Dyadic) * half ^ 12)⟩,
       ⟨((-1255 : Dyadic) * half ^ 14),
        ((1687 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word28Step19 :
    word28Chunk19.foldl (fun acc a => a.applyPacked acc)
      word28State19 = word28State20 := by decide +kernel

private def word28Chunk20 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word28State21 : PackedMat2 :=
    ⟨⟨⟨((8309 : Dyadic) * half ^ 14),
        ((15995 : Dyadic) * half ^ 16)⟩,
       ⟨((3731 : Dyadic) * half ^ 14),
        ((10341 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((10597 : Dyadic) * half ^ 15),
        ((-8227 : Dyadic) * half ^ 16)⟩,
       ⟨((17557 : Dyadic) * half ^ 15),
        ((-14569 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((10597 : Dyadic) * half ^ 15),
        ((-8227 : Dyadic) * half ^ 16)⟩,
       ⟨((-17557 : Dyadic) * half ^ 15),
        ((14569 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-8309 : Dyadic) * half ^ 14),
        ((-15995 : Dyadic) * half ^ 16)⟩,
       ⟨((3731 : Dyadic) * half ^ 14),
        ((10341 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word28Step20 :
    word28Chunk20.foldl (fun acc a => a.applyPacked acc)
      word28State20 = word28State21 := by decide +kernel

private def word28Chunk21 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word28State22 : PackedMat2 :=
    ⟨⟨⟨((-2865 : Dyadic) * half ^ 16),
        ((51049 : Dyadic) * half ^ 17)⟩,
       ⟨((15065 : Dyadic) * half ^ 15),
        ((23959 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-4869 : Dyadic) * half ^ 13),
        ((11683 : Dyadic) * half ^ 17)⟩,
       ⟨((-6799 : Dyadic) * half ^ 16),
        ((17731 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((189 : Dyadic) * half ^ 12),
        ((32153 : Dyadic) * half ^ 17)⟩,
       ⟨((14707 : Dyadic) * half ^ 16),
        ((-45751 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((13545 : Dyadic) * half ^ 16),
        ((-32995 : Dyadic) * half ^ 17)⟩,
       ⟨((-293 : Dyadic) * half ^ 9),
        ((-27265 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word28Step21 :
    word28Chunk21.foldl (fun acc a => a.applyPacked acc)
      word28State21 = word28State22 := by decide +kernel

private def word28Chunk22 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word28State23 : PackedMat2 :=
    ⟨⟨⟨((-18033 : Dyadic) * half ^ 17),
        ((-9003 : Dyadic) * half ^ 17)⟩,
       ⟨((27893 : Dyadic) * half ^ 17),
        ((46789 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((21347 : Dyadic) * half ^ 17),
        ((-36671 : Dyadic) * half ^ 16)⟩,
       ⟨((8909 : Dyadic) * half ^ 17),
        ((5511 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((3895 : Dyadic) * half ^ 13),
        ((-1891 : Dyadic) * half ^ 14)⟩,
       ⟨((21091 : Dyadic) * half ^ 15),
        ((-6219 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((18893 : Dyadic) * half ^ 16),
        ((2465 : Dyadic) * half ^ 16)⟩,
       ⟨((-3487 : Dyadic) * half ^ 13),
        ((-22963 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word28Step22 :
    word28Chunk22.foldl (fun acc a => a.applyPacked acc)
      word28State22 = word28State23 := by decide +kernel

private def word28Chunk23 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word28State24 : PackedMat2 :=
    ⟨⟨⟨((16421 : Dyadic) * half ^ 18),
        ((-39975 : Dyadic) * half ^ 17)⟩,
       ⟨((159909 : Dyadic) * half ^ 18),
        ((12671 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-117807 : Dyadic) * half ^ 18),
        ((15255 : Dyadic) * half ^ 18)⟩,
       ⟨((-12401 : Dyadic) * half ^ 18),
        ((-21849 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-117807 : Dyadic) * half ^ 18),
        ((15255 : Dyadic) * half ^ 18)⟩,
       ⟨((12401 : Dyadic) * half ^ 18),
        ((21849 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-16421 : Dyadic) * half ^ 18),
        ((39975 : Dyadic) * half ^ 17)⟩,
       ⟨((159909 : Dyadic) * half ^ 18),
        ((12671 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word28Step23 :
    word28Chunk23.foldl (fun acc a => a.applyPacked acc)
      word28State23 = word28State24 := by decide +kernel

private def word28Chunk24 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word28State25 : PackedMat2 :=
    ⟨⟨⟨((-194813 : Dyadic) * half ^ 19),
        ((-70305 : Dyadic) * half ^ 18)⟩,
       ⟨((-33253 : Dyadic) * half ^ 19),
        ((134339 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-94965 : Dyadic) * half ^ 19),
        ((3765 : Dyadic) * half ^ 19)⟩,
       ⟨((379561 : Dyadic) * half ^ 19),
        ((-29729 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((55693 : Dyadic) * half ^ 19),
        ((-71149 : Dyadic) * half ^ 18)⟩,
       ⟨((-63223 : Dyadic) * half ^ 19),
        ((237263 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-6271 : Dyadic) * half ^ 19),
        ((-114033 : Dyadic) * half ^ 19)⟩,
       ⟨((-274949 : Dyadic) * half ^ 19),
        ((-20195 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word28Step24 :
    word28Chunk24.foldl (fun acc a => a.applyPacked acc)
      word28State24 = word28State25 := by decide +kernel

private def word28Chunk25 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word28State26 : PackedMat2 :=
    ⟨⟨⟨((-606161 : Dyadic) * half ^ 20),
        ((-229223 : Dyadic) * half ^ 20)⟩,
       ⟨((167397 : Dyadic) * half ^ 20),
        ((-29047 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((285285 : Dyadic) * half ^ 20),
        ((-118663 : Dyadic) * half ^ 18)⟩,
       ⟨((-36055 : Dyadic) * half ^ 20),
        ((-171677 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-646329 : Dyadic) * half ^ 20),
        ((124615 : Dyadic) * half ^ 20)⟩,
       ⟨((-302975 : Dyadic) * half ^ 20),
        ((80335 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((287317 : Dyadic) * half ^ 20),
        ((109691 : Dyadic) * half ^ 19)⟩,
       ⟨((171129 : Dyadic) * half ^ 20),
        ((386779 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word28Step25 :
    word28Chunk25.foldl (fun acc a => a.applyPacked acc)
      word28State25 = word28State26 := by decide +kernel

private def word28Chunk26 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word28State27 : PackedMat2 :=
    ⟨⟨⟨((-170279 : Dyadic) * half ^ 20),
        ((-1022719 : Dyadic) * half ^ 21)⟩,
       ⟨((-343147 : Dyadic) * half ^ 20),
        ((109851 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-19193 : Dyadic) * half ^ 17),
        ((686185 : Dyadic) * half ^ 21)⟩,
       ⟨((6833 : Dyadic) * half ^ 17),
        ((-568801 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((19193 : Dyadic) * half ^ 17),
        ((-686185 : Dyadic) * half ^ 21)⟩,
       ⟨((6833 : Dyadic) * half ^ 17),
        ((-568801 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-170279 : Dyadic) * half ^ 20),
        ((-1022719 : Dyadic) * half ^ 21)⟩,
       ⟨((343147 : Dyadic) * half ^ 20),
        ((-109851 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word28Step26 :
    word28Chunk26.foldl (fun acc a => a.applyPacked acc)
      word28State26 = word28State27 := by decide +kernel

private def word28Chunk27 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word28State28 : PackedMat2 :=
    ⟨⟨⟨((-1307065 : Dyadic) * half ^ 21),
        ((-242201 : Dyadic) * half ^ 22)⟩,
       ⟨((-217 : Dyadic) * half ^ 18),
        ((-1807893 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((16309 : Dyadic) * half ^ 19),
        ((434581 : Dyadic) * half ^ 22)⟩,
       ⟨((-265911 : Dyadic) * half ^ 21),
        ((1308939 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-437179 : Dyadic) * half ^ 21),
        ((331147 : Dyadic) * half ^ 22)⟩,
       ⟨((-54485 : Dyadic) * half ^ 17),
        ((200675 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-391423 : Dyadic) * half ^ 20),
        ((1305329 : Dyadic) * half ^ 22)⟩,
       ⟨((-1025047 : Dyadic) * half ^ 21),
        ((-1308801 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word28Step27 :
    word28Chunk27.foldl (fun acc a => a.applyPacked acc)
      word28State27 = word28State28 := by decide +kernel

private def word28Chunk28 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word28State29 : PackedMat2 :=
    ⟨⟨⟨((-175229 : Dyadic) * half ^ 22),
        ((-46457 : Dyadic) * half ^ 20)⟩,
       ⟨((-2849047 : Dyadic) * half ^ 22),
        ((-388653 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((2007557 : Dyadic) * half ^ 22),
        ((-468133 : Dyadic) * half ^ 22)⟩,
       ⟨((1372439 : Dyadic) * half ^ 22),
        ((-952567 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-355175 : Dyadic) * half ^ 20),
        ((844999 : Dyadic) * half ^ 21)⟩,
       ⟨((242217 : Dyadic) * half ^ 21),
        ((317559 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((481567 : Dyadic) * half ^ 21),
        ((756069 : Dyadic) * half ^ 21)⟩,
       ⟨((-295739 : Dyadic) * half ^ 21),
        ((-1336909 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word28Step28 :
    word28Chunk28.foldl (fun acc a => a.applyPacked acc)
      word28State28 = word28State29 := by decide +kernel

private def word28Chunk29 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word28State30 : PackedMat2 :=
    ⟨⟨⟨((3898091 : Dyadic) * half ^ 23),
        ((-1087921 : Dyadic) * half ^ 23)⟩,
       ⟨((-2214275 : Dyadic) * half ^ 23),
        ((-1676217 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-3271839 : Dyadic) * half ^ 23),
        ((723993 : Dyadic) * half ^ 22)⟩,
       ⟨((693901 : Dyadic) * half ^ 23),
        ((2241215 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((3271839 : Dyadic) * half ^ 23),
        ((-723993 : Dyadic) * half ^ 22)⟩,
       ⟨((693901 : Dyadic) * half ^ 23),
        ((2241215 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((3898091 : Dyadic) * half ^ 23),
        ((-1087921 : Dyadic) * half ^ 23)⟩,
       ⟨((2214275 : Dyadic) * half ^ 23),
        ((1676217 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word28Step29 :
    word28Chunk29.foldl (fun acc a => a.applyPacked acc)
      word28State29 = word28State30 := by decide +kernel

private def word28Chunk30 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word28State31 : PackedMat2 :=
    ⟨⟨⟨((6513935 : Dyadic) * half ^ 24),
        ((-4752577 : Dyadic) * half ^ 24)⟩,
       ⟨((-2915319 : Dyadic) * half ^ 24),
        ((2545269 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-2142619 : Dyadic) * half ^ 24),
        ((-1458793 : Dyadic) * half ^ 23)⟩,
       ⟨((7613393 : Dyadic) * half ^ 24),
        ((5194431 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((2276845 : Dyadic) * half ^ 24),
        ((2735387 : Dyadic) * half ^ 24)⟩,
       ⟨((-8112017 : Dyadic) * half ^ 24),
        ((-2439003 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-337961 : Dyadic) * half ^ 24),
        ((-449827 : Dyadic) * half ^ 22)⟩,
       ⟨((9843115 : Dyadic) * half ^ 24),
        ((-4714627 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word28Step30 :
    word28Chunk30.foldl (fun acc a => a.applyPacked acc)
      word28State30 = word28State31 := by decide +kernel

private def word28Chunk31 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word28State32 : PackedMat2 :=
    ⟨⟨⟨((-5582443 : Dyadic) * half ^ 24),
        ((7112053 : Dyadic) * half ^ 25)⟩,
       ⟨((827599 : Dyadic) * half ^ 24),
        ((-12921813 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-870047 : Dyadic) * half ^ 21),
        ((-8954159 : Dyadic) * half ^ 25)⟩,
       ⟨((590987 : Dyadic) * half ^ 23),
        ((-10091257 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((870047 : Dyadic) * half ^ 21),
        ((8954159 : Dyadic) * half ^ 25)⟩,
       ⟨((590987 : Dyadic) * half ^ 23),
        ((-10091257 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-5582443 : Dyadic) * half ^ 24),
        ((7112053 : Dyadic) * half ^ 25)⟩,
       ⟨((-827599 : Dyadic) * half ^ 24),
        ((12921813 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word28Step31 :
    word28Chunk31.foldl (fun acc a => a.applyPacked acc)
      word28State31 = word28State32 := by decide +kernel

private def word28Chunk32 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word28State33 : PackedMat2 :=
    ⟨⟨⟨((-8137649 : Dyadic) * half ^ 24),
        ((6324863 : Dyadic) * half ^ 26)⟩,
       ⟨((-15953751 : Dyadic) * half ^ 25),
        ((10691539 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-12082615 : Dyadic) * half ^ 25),
        ((-11753357 : Dyadic) * half ^ 26)⟩,
       ⟨((-689919 : Dyadic) * half ^ 22),
        ((-23824879 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((6035761 : Dyadic) * half ^ 25),
        ((-6563263 : Dyadic) * half ^ 26)⟩,
       ⟨((8894559 : Dyadic) * half ^ 24),
        ((17601967 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((1091669 : Dyadic) * half ^ 24),
        ((321547 : Dyadic) * half ^ 26)⟩,
       ⟨((8508201 : Dyadic) * half ^ 25),
        ((-32229049 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word28Step32 :
    word28Chunk32.foldl (fun acc a => a.applyPacked acc)
      word28State32 = word28State33 := by decide +kernel

private def word28Chunk33 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word28State34 : PackedMat2 :=
    ⟨⟨⟨((10195999 : Dyadic) * half ^ 26),
        ((-13748873 : Dyadic) * half ^ 25)⟩,
       ⟨((-64407 : Dyadic) * half ^ 26),
        ((-27465 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((10041293 : Dyadic) * half ^ 26),
        ((-3332607 : Dyadic) * half ^ 26)⟩,
       ⟨((-51861245 : Dyadic) * half ^ 26),
        ((-6050261 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-51861245 : Dyadic) * half ^ 26),
        ((-6050261 : Dyadic) * half ^ 26)⟩,
       ⟨((10041293 : Dyadic) * half ^ 26),
        ((-3332607 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((64407 : Dyadic) * half ^ 26),
        ((27465 : Dyadic) * half ^ 21)⟩,
       ⟨((-10195999 : Dyadic) * half ^ 26),
        ((13748873 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word28Step33 :
    word28Chunk33.foldl (fun acc a => a.applyPacked acc)
      word28State33 = word28State34 := by decide +kernel

private def word28Chunk34 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word28State35 : PackedMat2 :=
    ⟨⟨⟨((-57648739 : Dyadic) * half ^ 27),
        ((-9938195 : Dyadic) * half ^ 26)⟩,
       ⟨((-944629 : Dyadic) * half ^ 27),
        ((-48472129 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((18577165 : Dyadic) * half ^ 27),
        ((21221757 : Dyadic) * half ^ 27)⟩,
       ⟨((26317397 : Dyadic) * half ^ 27),
        ((-941557 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-18577165 : Dyadic) * half ^ 27),
        ((-21221757 : Dyadic) * half ^ 27)⟩,
       ⟨((26317397 : Dyadic) * half ^ 27),
        ((-941557 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-57648739 : Dyadic) * half ^ 27),
        ((-9938195 : Dyadic) * half ^ 26)⟩,
       ⟨((944629 : Dyadic) * half ^ 27),
        ((48472129 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word28Step34 :
    word28Chunk34.foldl (fun acc a => a.applyPacked acc)
      word28State34 = word28State35 := by decide +kernel

private def word28Chunk35 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word28State36 : PackedMat2 :=
    ⟨⟨⟨((-14346329 : Dyadic) * half ^ 26),
        ((-30398367 : Dyadic) * half ^ 28)⟩,
       ⟨((-8017225 : Dyadic) * half ^ 24),
        ((-81080667 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-20761311 : Dyadic) * half ^ 27),
        ((58960423 : Dyadic) * half ^ 28)⟩,
       ⟨((-50498751 : Dyadic) * half ^ 27),
        ((96011283 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-9262715 : Dyadic) * half ^ 26),
        ((929295 : Dyadic) * half ^ 23)⟩,
       ⟨((-77485853 : Dyadic) * half ^ 27),
        ((35630031 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-12670575 : Dyadic) * half ^ 26),
        ((-17722571 : Dyadic) * half ^ 27)⟩,
       ⟨((-55739517 : Dyadic) * half ^ 27),
        ((-46415229 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word28Step35 :
    word28Chunk35.foldl (fun acc a => a.applyPacked acc)
      word28State35 = word28State36 := by decide +kernel

private def word28Chunk36 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word28State37 : PackedMat2 :=
    ⟨⟨⟨((15214003 : Dyadic) * half ^ 28),
        ((53432791 : Dyadic) * half ^ 29)⟩,
       ⟨((-93629589 : Dyadic) * half ^ 27),
        ((-87413905 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((10514753 : Dyadic) * half ^ 25),
        ((-172979047 : Dyadic) * half ^ 29)⟩,
       ⟨((19510455 : Dyadic) * half ^ 28),
        ((-134867537 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((19510455 : Dyadic) * half ^ 28),
        ((-134867537 : Dyadic) * half ^ 29)⟩,
       ⟨((10514753 : Dyadic) * half ^ 25),
        ((-172979047 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((93629589 : Dyadic) * half ^ 27),
        ((87413905 : Dyadic) * half ^ 29)⟩,
       ⟨((-15214003 : Dyadic) * half ^ 28),
        ((-53432791 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word28Step36 :
    word28Chunk36.foldl (fun acc a => a.applyPacked acc)
      word28State36 = word28State37 := by decide +kernel

private def word28Chunk37 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word28State38 : PackedMat2 :=
    ⟨⟨⟨((1561023 : Dyadic) * half ^ 26),
        ((238328965 : Dyadic) * half ^ 30)⟩,
       ⟨((-145696491 : Dyadic) * half ^ 29),
        ((-162192251 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((229921793 : Dyadic) * half ^ 29),
        ((95423557 : Dyadic) * half ^ 30)⟩,
       ⟨((-200334793 : Dyadic) * half ^ 28),
        ((121164907 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-12870675 : Dyadic) * half ^ 29),
        ((630591379 : Dyadic) * half ^ 30)⟩,
       ⟨((-13536779 : Dyadic) * half ^ 26),
        ((170747793 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-195567 : Dyadic) * half ^ 19),
        ((-158184675 : Dyadic) * half ^ 30)⟩,
       ⟨((38068357 : Dyadic) * half ^ 29),
        ((-133208307 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word28Step37 :
    word28Chunk37.foldl (fun acc a => a.applyPacked acc)
      word28State37 = word28State38 := by decide +kernel

private def word28Chunk38 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word28State39 : PackedMat2 :=
    ⟨⟨⟨((154103663 : Dyadic) * half ^ 30),
        ((45872531 : Dyadic) * half ^ 30)⟩,
       ⟨((-550373653 : Dyadic) * half ^ 30),
        ((34050445 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((508581327 : Dyadic) * half ^ 30),
        ((144251911 : Dyadic) * half ^ 29)⟩,
       ⟨((496783191 : Dyadic) * half ^ 30),
        ((-135930841 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((4160535 : Dyadic) * half ^ 28),
        ((502682259 : Dyadic) * half ^ 30)⟩,
       ⟨((8755711 : Dyadic) * half ^ 24),
        ((1474767 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-2497593 : Dyadic) * half ^ 25),
        ((198134995 : Dyadic) * half ^ 30)⟩,
       ⟨((-5911043 : Dyadic) * half ^ 29),
        ((-176119329 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word28Step38 :
    word28Chunk38.foldl (fun acc a => a.applyPacked acc)
      word28State38 = word28State39 := by decide +kernel

private def word28Chunk39 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word28State40 : PackedMat2 :=
    ⟨⟨⟨((916673403 : Dyadic) * half ^ 31),
        ((35051219 : Dyadic) * half ^ 27)⟩,
       ⟨((287617101 : Dyadic) * half ^ 31),
        ((85548773 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-599102677 : Dyadic) * half ^ 31),
        ((-56615603 : Dyadic) * half ^ 31)⟩,
       ⟨((-521933377 : Dyadic) * half ^ 31),
        ((34284319 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((599102677 : Dyadic) * half ^ 31),
        ((56615603 : Dyadic) * half ^ 31)⟩,
       ⟨((-521933377 : Dyadic) * half ^ 31),
        ((34284319 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((916673403 : Dyadic) * half ^ 31),
        ((35051219 : Dyadic) * half ^ 27)⟩,
       ⟨((-287617101 : Dyadic) * half ^ 31),
        ((-85548773 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word28Step39 :
    word28Chunk39.foldl (fun acc a => a.applyPacked acc)
      word28State39 = word28State40 := by decide +kernel

private def word28Chunk40 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word28State41 : PackedMat2 :=
    ⟨⟨⟨((179140573 : Dyadic) * half ^ 29),
        ((887740233 : Dyadic) * half ^ 32)⟩,
       ⟨((141459393 : Dyadic) * half ^ 30),
        ((1945534813 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((662687787 : Dyadic) * half ^ 31),
        ((-1135381381 : Dyadic) * half ^ 32)⟩,
       ⟨((653738319 : Dyadic) * half ^ 31),
        ((-664097753 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-117820907 : Dyadic) * half ^ 30),
        ((2237367 : Dyadic) * half ^ 30)⟩,
       ⟨((899739567 : Dyadic) * half ^ 31),
        ((-658213053 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((264448645 : Dyadic) * half ^ 30),
        ((-216821753 : Dyadic) * half ^ 31)⟩,
       ⟨((1416637523 : Dyadic) * half ^ 31),
        ((499740539 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word28Step40 :
    word28Chunk40.foldl (fun acc a => a.applyPacked acc)
      word28State40 = word28State41 := by decide +kernel

private def word28Chunk41 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word28State42 : PackedMat2 :=
    ⟨⟨⟨((840463261 : Dyadic) * half ^ 32),
        ((-521359697 : Dyadic) * half ^ 33)⟩,
       ⟨((881178769 : Dyadic) * half ^ 31),
        ((2770003911 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1159008495 : Dyadic) * half ^ 31),
        ((2423116833 : Dyadic) * half ^ 33)⟩,
       ⟨((-1418047489 : Dyadic) * half ^ 32),
        ((-827385821 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1418047489 : Dyadic) * half ^ 32),
        ((-827385821 : Dyadic) * half ^ 33)⟩,
       ⟨((-1159008495 : Dyadic) * half ^ 31),
        ((2423116833 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-881178769 : Dyadic) * half ^ 31),
        ((-2770003911 : Dyadic) * half ^ 33)⟩,
       ⟨((-840463261 : Dyadic) * half ^ 32),
        ((521359697 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word28Step41 :
    word28Chunk41.foldl (fun acc a => a.applyPacked acc)
      word28State41 = word28State42 := by decide +kernel

private def word28Chunk42 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word28State43 : PackedMat2 :=
    ⟨⟨⟨((-4085076489 : Dyadic) * half ^ 33),
        ((-813516543 : Dyadic) * half ^ 34)⟩,
       ⟨((484852607 : Dyadic) * half ^ 31),
        ((4941993117 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1958199539 : Dyadic) * half ^ 32),
        ((5182556803 : Dyadic) * half ^ 34)⟩,
       ⟨((-2998576129 : Dyadic) * half ^ 33),
        ((-2464213039 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((3823384921 : Dyadic) * half ^ 33),
        ((-917822949 : Dyadic) * half ^ 34)⟩,
       ⟨((-679585941 : Dyadic) * half ^ 32),
        ((6914975207 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((1438877415 : Dyadic) * half ^ 32),
        ((6024486917 : Dyadic) * half ^ 34)⟩,
       ⟨((2064238287 : Dyadic) * half ^ 33),
        ((-2145666061 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word28Step42 :
    word28Chunk42.foldl (fun acc a => a.applyPacked acc)
      word28State42 = word28State43 := by decide +kernel

private def word28Chunk43 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word28State44 : PackedMat2 :=
    ⟨⟨⟨((386412019 : Dyadic) * half ^ 31),
        ((-1383848305 : Dyadic) * half ^ 32)⟩,
       ⟨((-166231891 : Dyadic) * half ^ 29),
        ((-493100257 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((6808057479 : Dyadic) * half ^ 33),
        ((597080051 : Dyadic) * half ^ 33)⟩,
       ⟨((626396805 : Dyadic) * half ^ 32),
        ((-706935713 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((626396805 : Dyadic) * half ^ 32),
        ((-706935713 : Dyadic) * half ^ 34)⟩,
       ⟨((6808057479 : Dyadic) * half ^ 33),
        ((597080051 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((166231891 : Dyadic) * half ^ 29),
        ((493100257 : Dyadic) * half ^ 34)⟩,
       ⟨((-386412019 : Dyadic) * half ^ 31),
        ((1383848305 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word28Step43 :
    word28Chunk43.foldl (fun acc a => a.applyPacked acc)
      word28State43 = word28State44 := by decide +kernel

private def word28Chunk44 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word28State45 : PackedMat2 :=
    ⟨⟨⟨((-7652461743 : Dyadic) * half ^ 35),
        ((-492716865 : Dyadic) * half ^ 33)⟩,
       ⟨((2592320027 : Dyadic) * half ^ 35),
        ((-2793962643 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-5159559979 : Dyadic) * half ^ 35),
        ((18528409003 : Dyadic) * half ^ 35)⟩,
       ⟨((18230737009 : Dyadic) * half ^ 35),
        ((2406904751 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-23342218505 : Dyadic) * half ^ 35),
        ((-6535588515 : Dyadic) * half ^ 35)⟩,
       ⟨((-13714599501 : Dyadic) * half ^ 35),
        ((5847574247 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-4764830103 : Dyadic) * half ^ 35),
        ((-1265035429 : Dyadic) * half ^ 34)⟩,
       ⟨((823095183 : Dyadic) * half ^ 35),
        ((-5122390885 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word28Step44 :
    word28Chunk44.foldl (fun acc a => a.applyPacked acc)
      word28State44 = word28State45 := by decide +kernel

private def word28Chunk45 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word28State46 : PackedMat2 :=
    ⟨⟨⟨((-323753093 : Dyadic) * half ^ 34),
        ((-13402124169 : Dyadic) * half ^ 36)⟩,
       ⟨((-7306363851 : Dyadic) * half ^ 34),
        ((-6178027733 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-435586833 : Dyadic) * half ^ 35),
        ((25372578901 : Dyadic) * half ^ 36)⟩,
       ⟨((-2704126287 : Dyadic) * half ^ 35),
        ((32507296141 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-891839655 : Dyadic) * half ^ 33),
        ((1134269727 : Dyadic) * half ^ 35)⟩,
       ⟨((-28939937521 : Dyadic) * half ^ 35),
        ((98116035 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((1806024109 : Dyadic) * half ^ 34),
        ((-3491305379 : Dyadic) * half ^ 34)⟩,
       ⟨((-9790075951 : Dyadic) * half ^ 35),
        ((-476882309 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word28Step45 :
    word28Chunk45.foldl (fun acc a => a.applyPacked acc)
      word28State45 = word28State46 := by decide +kernel

private def word28Chunk46 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word28State47 : PackedMat2 :=
    ⟨⟨⟨((3007971193 : Dyadic) * half ^ 36),
        ((35595541893 : Dyadic) * half ^ 37)⟩,
       ⟨((-57742988707 : Dyadic) * half ^ 36),
        ((5241022819 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((14965327 : Dyadic) * half ^ 33),
        ((28116424429 : Dyadic) * half ^ 37)⟩,
       ⟨((-2077420213 : Dyadic) * half ^ 34),
        ((-23129141585 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-14965327 : Dyadic) * half ^ 33),
        ((-28116424429 : Dyadic) * half ^ 37)⟩,
       ⟨((-2077420213 : Dyadic) * half ^ 34),
        ((-23129141585 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((3007971193 : Dyadic) * half ^ 36),
        ((35595541893 : Dyadic) * half ^ 37)⟩,
       ⟨((57742988707 : Dyadic) * half ^ 36),
        ((-5241022819 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word28Step46 :
    word28Chunk46.foldl (fun acc a => a.applyPacked acc)
      word28State46 = word28State47 := by decide +kernel

private def word28Chunk47 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word28State48 : PackedMat2 :=
    ⟨⟨⟨((69792554435 : Dyadic) * half ^ 37),
        ((-8202029241 : Dyadic) * half ^ 38)⟩,
       ⟨((18214890351 : Dyadic) * half ^ 35),
        ((-47509640025 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((9205178109 : Dyadic) * half ^ 35),
        ((39037662517 : Dyadic) * half ^ 38)⟩,
       ⟨((68666033597 : Dyadic) * half ^ 37),
        ((37814584959 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((611538779 : Dyadic) * half ^ 37),
        ((-31845321161 : Dyadic) * half ^ 38)⟩,
       ⟨((-19213061869 : Dyadic) * half ^ 36),
        ((-105486746033 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-1228362837 : Dyadic) * half ^ 33),
        ((3067006969 : Dyadic) * half ^ 38)⟩,
       ⟨((-27855834633 : Dyadic) * half ^ 37),
        ((142652115839 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word28Step47 :
    word28Chunk47.foldl (fun acc a => a.applyPacked acc)
      word28State47 = word28State48 := by decide +kernel

private def word28Chunk48 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word28State49 : PackedMat2 :=
    ⟨⟨⟨((204740546403 : Dyadic) * half ^ 38),
        ((-944101761 : Dyadic) * half ^ 36)⟩,
       ⟨((129945618011 : Dyadic) * half ^ 38),
        ((-21692152819 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-46609138073 : Dyadic) * half ^ 38),
        ((-80795779665 : Dyadic) * half ^ 38)⟩,
       ⟨((-20168787451 : Dyadic) * half ^ 38),
        ((2154787501 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-46609138073 : Dyadic) * half ^ 38),
        ((-80795779665 : Dyadic) * half ^ 38)⟩,
       ⟨((20168787451 : Dyadic) * half ^ 38),
        ((-2154787501 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-204740546403 : Dyadic) * half ^ 38),
        ((944101761 : Dyadic) * half ^ 36)⟩,
       ⟨((129945618011 : Dyadic) * half ^ 38),
        ((-21692152819 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word28Step48 :
    word28Chunk48.foldl (fun acc a => a.applyPacked acc)
      word28State48 = word28State49 := by decide +kernel

private def word28Chunk49 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word28State50 : PackedMat2 :=
    ⟨⟨⟨((-45444647013 : Dyadic) * half ^ 38),
        ((307228478887 : Dyadic) * half ^ 39)⟩,
       ⟨((70593726657 : Dyadic) * half ^ 38),
        ((134788360971 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((15829443631 : Dyadic) * half ^ 37),
        ((-59004695121 : Dyadic) * half ^ 39)⟩,
       ⟨((-39829114019 : Dyadic) * half ^ 37),
        ((-79272414297 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-2533464897 : Dyadic) * half ^ 36),
        ((-27829278825 : Dyadic) * half ^ 37)⟩,
       ⟨((-69138554709 : Dyadic) * half ^ 38),
        ((-5999917597 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((43110029479 : Dyadic) * half ^ 37),
        ((-58019186835 : Dyadic) * half ^ 38)⟩,
       ⟨((-221008419929 : Dyadic) * half ^ 38),
        ((-6287269911 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word28Step49 :
    word28Chunk49.foldl (fun acc a => a.applyPacked acc)
      word28State49 = word28State50 := by decide +kernel

private def word28Chunk50 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word28State51 : PackedMat2 :=
    ⟨⟨⟨((-45443323181 : Dyadic) * half ^ 37),
        ((119627300767 : Dyadic) * half ^ 40)⟩,
       ⟨((19618295073 : Dyadic) * half ^ 37),
        ((-248416787715 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-155221477573 : Dyadic) * half ^ 39),
        ((333374484517 : Dyadic) * half ^ 40)⟩,
       ⟨((-321943411133 : Dyadic) * half ^ 39),
        ((-288827106213 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-155221477573 : Dyadic) * half ^ 39),
        ((333374484517 : Dyadic) * half ^ 40)⟩,
       ⟨((321943411133 : Dyadic) * half ^ 39),
        ((288827106213 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((45443323181 : Dyadic) * half ^ 37),
        ((-119627300767 : Dyadic) * half ^ 40)⟩,
       ⟨((19618295073 : Dyadic) * half ^ 37),
        ((-248416787715 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word28Step50 :
    word28Chunk50.foldl (fun acc a => a.applyPacked acc)
      word28State50 = word28State51 := by decide +kernel

private def word28Chunk51 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word28State52 : PackedMat2 :=
    ⟨⟨⟨((18880431323 : Dyadic) * half ^ 40),
        ((362035090973 : Dyadic) * half ^ 41)⟩,
       ⟨((-185322718951 : Dyadic) * half ^ 38),
        ((109851727791 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((36932697011 : Dyadic) * half ^ 36),
        ((-124915961365 : Dyadic) * half ^ 41)⟩,
       ⟨((-260026539545 : Dyadic) * half ^ 40),
        ((-570758810765 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-55730356175 : Dyadic) * half ^ 38),
        ((-850949691721 : Dyadic) * half ^ 41)⟩,
       ⟨((-347837386065 : Dyadic) * half ^ 40),
        ((330896612631 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((126091681591 : Dyadic) * half ^ 40),
        ((760171307127 : Dyadic) * half ^ 41)⟩,
       ⟨((-117971704691 : Dyadic) * half ^ 39),
        ((722410444481 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word28Step51 :
    word28Chunk51.foldl (fun acc a => a.applyPacked acc)
      word28State51 = word28State52 := by decide +kernel

private def word28Chunk52 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word28State53 : PackedMat2 :=
    ⟨⟨⟨((1694249118953 : Dyadic) * half ^ 41),
        ((-98503413255 : Dyadic) * half ^ 41)⟩,
       ⟨((388758698659 : Dyadic) * half ^ 41),
        ((-274893924935 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((116230146857 : Dyadic) * half ^ 41),
        ((86910626509 : Dyadic) * half ^ 38)⟩,
       ⟨((-721126534393 : Dyadic) * half ^ 41),
        ((-66889664083 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((721126534393 : Dyadic) * half ^ 41),
        ((66889664083 : Dyadic) * half ^ 39)⟩,
       ⟨((-116230146857 : Dyadic) * half ^ 41),
        ((-86910626509 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((388758698659 : Dyadic) * half ^ 41),
        ((-274893924935 : Dyadic) * half ^ 41)⟩,
       ⟨((1694249118953 : Dyadic) * half ^ 41),
        ((-98503413255 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word28Step52 :
    word28Chunk52.foldl (fun acc a => a.applyPacked acc)
      word28State52 = word28State53 := by decide +kernel

private def word28Chunk53 : List Letter := [.t, .h, .t]
private def word28State54 : PackedMat2 :=
    ⟨⟨⟨((160087463685 : Dyadic) * half ^ 40),
        ((2657092787357 : Dyadic) * half ^ 42)⟩,
       ⟨((27554268833 : Dyadic) * half ^ 41),
        ((-38967657081 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((42539801925 : Dyadic) * half ^ 41),
        ((-60160364823 : Dyadic) * half ^ 42)⟩,
       ⟨((386972626237 : Dyadic) * half ^ 40),
        ((-1094523872583 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-42539801925 : Dyadic) * half ^ 41),
        ((60160364823 : Dyadic) * half ^ 42)⟩,
       ⟨((386972626237 : Dyadic) * half ^ 40),
        ((-1094523872583 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((160087463685 : Dyadic) * half ^ 40),
        ((2657092787357 : Dyadic) * half ^ 42)⟩,
       ⟨((-27554268833 : Dyadic) * half ^ 41),
        ((38967657081 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word28Step53 :
    word28Chunk53.foldl (fun acc a => a.applyPacked acc)
      word28State53 = word28State54 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word28_check : check word28 28 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word28 = word28State54.toMatrix := by
    unfold evalRingPacked
    change ((
      word28Chunk0 ++ word28Chunk1 ++ word28Chunk2 ++ word28Chunk3 ++
      word28Chunk4 ++ word28Chunk5 ++ word28Chunk6 ++ word28Chunk7 ++
      word28Chunk8 ++ word28Chunk9 ++ word28Chunk10 ++ word28Chunk11 ++
      word28Chunk12 ++ word28Chunk13 ++ word28Chunk14 ++ word28Chunk15 ++
      word28Chunk16 ++ word28Chunk17 ++ word28Chunk18 ++ word28Chunk19 ++
      word28Chunk20 ++ word28Chunk21 ++ word28Chunk22 ++ word28Chunk23 ++
      word28Chunk24 ++ word28Chunk25 ++ word28Chunk26 ++ word28Chunk27 ++
      word28Chunk28 ++ word28Chunk29 ++ word28Chunk30 ++ word28Chunk31 ++
      word28Chunk32 ++ word28Chunk33 ++ word28Chunk34 ++ word28Chunk35 ++
      word28Chunk36 ++ word28Chunk37 ++ word28Chunk38 ++ word28Chunk39 ++
      word28Chunk40 ++ word28Chunk41 ++ word28Chunk42 ++ word28Chunk43 ++
      word28Chunk44 ++ word28Chunk45 ++ word28Chunk46 ++ word28Chunk47 ++
      word28Chunk48 ++ word28Chunk49 ++ word28Chunk50 ++ word28Chunk51 ++
      word28Chunk52 ++ word28Chunk53
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word28Step0, word28Step1, word28Step2, word28Step3, word28Step4,
      word28Step5, word28Step6, word28Step7, word28Step8, word28Step9,
      word28Step10, word28Step11, word28Step12, word28Step13, word28Step14,
      word28Step15, word28Step16, word28Step17, word28Step18, word28Step19,
      word28Step20, word28Step21, word28Step22, word28Step23, word28Step24,
      word28Step25, word28Step26, word28Step27, word28Step28, word28Step29,
      word28Step30, word28Step31, word28Step32, word28Step33, word28Step34,
      word28Step35, word28Step36, word28Step37, word28Step38, word28Step39,
      word28Step40, word28Step41, word28Step42, word28Step43, word28Step44,
      word28Step45, word28Step46, word28Step47, word28Step48, word28Step49,
      word28Step50, word28Step51, word28Step52, word28Step53]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
