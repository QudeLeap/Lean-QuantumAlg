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
private def word25Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word25State1 : PackedMat2 :=
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
private lemma word25Step0 :
    word25Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word25State1 := by decide +kernel

private def word25Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word25State2 : PackedMat2 :=
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
private lemma word25Step1 :
    word25Chunk1.foldl (fun acc a => a.applyPacked acc)
      word25State1 = word25State2 := by decide +kernel

private def word25Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word25State3 : PackedMat2 :=
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
private lemma word25Step2 :
    word25Chunk2.foldl (fun acc a => a.applyPacked acc)
      word25State2 = word25State3 := by decide +kernel

private def word25Chunk3 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word25State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word25Step3 :
    word25Chunk3.foldl (fun acc a => a.applyPacked acc)
      word25State3 = word25State4 := by decide +kernel

private def word25Chunk4 : List Letter := [.h, .s, .h, .s, .h, .s, .s, .h]
private def word25State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(-1 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(-1 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word25Step4 :
    word25Chunk4.foldl (fun acc a => a.applyPacked acc)
      word25State4 = word25State5 := by decide +kernel

private def word25Chunk5 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word25State6 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word25Step5 :
    word25Chunk5.foldl (fun acc a => a.applyPacked acc)
      word25State5 = word25State6 := by decide +kernel

private def word25Chunk6 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word25State7 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word25Step6 :
    word25Chunk6.foldl (fun acc a => a.applyPacked acc)
      word25State6 = word25State7 := by decide +kernel

private def word25Chunk7 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word25State8 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((5 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((7 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word25Step7 :
    word25Chunk7.foldl (fun acc a => a.applyPacked acc)
      word25State7 = word25State8 := by decide +kernel

private def word25Chunk8 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word25State9 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word25Step8 :
    word25Chunk8.foldl (fun acc a => a.applyPacked acc)
      word25State8 = word25State9 := by decide +kernel

private def word25Chunk9 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word25State10 : PackedMat2 :=
    ⟨⟨⟨((-7 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 5),
        ((15 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 4)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((-7 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((15 : Dyadic) * half ^ 5)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word25Step9 :
    word25Chunk9.foldl (fun acc a => a.applyPacked acc)
      word25State9 = word25State10 := by decide +kernel

private def word25Chunk10 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word25State11 : PackedMat2 :=
    ⟨⟨⟨((-19 : Dyadic) * half ^ 6),
        ((-19 : Dyadic) * half ^ 6)⟩,
       ⟨((9 : Dyadic) * half ^ 6),
        ((-17 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 6)⟩,
       ⟨((-3 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 6)⟩,
       ⟨((-23 : Dyadic) * half ^ 6),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((53 : Dyadic) * half ^ 6),
        ((5 : Dyadic) * half ^ 6)⟩,
       ⟨((-15 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word25Step10 :
    word25Chunk10.foldl (fun acc a => a.applyPacked acc)
      word25State10 = word25State11 := by decide +kernel

private def word25Chunk11 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word25State12 : PackedMat2 :=
    ⟨⟨⟨((7 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 7)⟩,
       ⟨((15 : Dyadic) * half ^ 6),
        ((-33 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 5),
        ((-39 : Dyadic) * half ^ 7)⟩,
       ⟨((9 : Dyadic) * half ^ 6),
        ((57 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 6),
        ((57 : Dyadic) * half ^ 7)⟩,
       ⟨((-3 : Dyadic) * half ^ 5),
        ((-39 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 6),
        ((33 : Dyadic) * half ^ 7)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((9 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word25Step11 :
    word25Chunk11.foldl (fun acc a => a.applyPacked acc)
      word25State11 = word25State12 := by decide +kernel

private def word25Chunk12 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word25State13 : PackedMat2 :=
    ⟨⟨⟨((-11 : Dyadic) * half ^ 6),
        ((29 : Dyadic) * half ^ 7)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-15 : Dyadic) * half ^ 6),
        ((-19 : Dyadic) * half ^ 6)⟩,
       ⟨((-9 : Dyadic) * half ^ 6),
        ((-53 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((9 : Dyadic) * half ^ 6),
        ((53 : Dyadic) * half ^ 7)⟩,
       ⟨((15 : Dyadic) * half ^ 6),
        ((19 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((13 : Dyadic) * half ^ 6)⟩,
       ⟨((-11 : Dyadic) * half ^ 6),
        ((29 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word25Step12 :
    word25Chunk12.foldl (fun acc a => a.applyPacked acc)
      word25State12 = word25State13 := by decide +kernel

private def word25Chunk13 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word25State14 : PackedMat2 :=
    ⟨⟨⟨((129 : Dyadic) * half ^ 8),
        ((-27 : Dyadic) * half ^ 7)⟩,
       ⟨((121 : Dyadic) * half ^ 8),
        ((-3 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-61 : Dyadic) * half ^ 8),
        ((3 : Dyadic) * half ^ 7)⟩,
       ⟨((-81 : Dyadic) * half ^ 8),
        ((-95 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-61 : Dyadic) * half ^ 8),
        ((3 : Dyadic) * half ^ 7)⟩,
       ⟨((81 : Dyadic) * half ^ 8),
        ((95 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-129 : Dyadic) * half ^ 8),
        ((27 : Dyadic) * half ^ 7)⟩,
       ⟨((121 : Dyadic) * half ^ 8),
        ((-3 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word25Step13 :
    word25Chunk13.foldl (fun acc a => a.applyPacked acc)
      word25State13 = word25State14 := by decide +kernel

private def word25Chunk14 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word25State15 : PackedMat2 :=
    ⟨⟨⟨((55 : Dyadic) * half ^ 9),
        ((-35 : Dyadic) * half ^ 7)⟩,
       ⟨((209 : Dyadic) * half ^ 9),
        ((185 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((131 : Dyadic) * half ^ 9),
        ((-21 : Dyadic) * half ^ 6)⟩,
       ⟨((169 : Dyadic) * half ^ 9),
        ((-53 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((221 : Dyadic) * half ^ 9),
        ((-75 : Dyadic) * half ^ 8)⟩,
       ⟨((115 : Dyadic) * half ^ 9),
        ((19 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 9),
        ((33 : Dyadic) * half ^ 7)⟩,
       ⟨((-325 : Dyadic) * half ^ 9),
        ((-77 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word25Step14 :
    word25Chunk14.foldl (fun acc a => a.applyPacked acc)
      word25State14 = word25State15 := by decide +kernel

private def word25Chunk15 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word25State16 : PackedMat2 :=
    ⟨⟨⟨((-329 : Dyadic) * half ^ 9),
        ((-77 : Dyadic) * half ^ 10)⟩,
       ⟨((147 : Dyadic) * half ^ 9),
        ((237 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-37 : Dyadic) * half ^ 7),
        ((369 : Dyadic) * half ^ 10)⟩,
       ⟨((5 : Dyadic) * half ^ 6),
        ((-139 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((127 : Dyadic) * half ^ 8),
        ((-47 : Dyadic) * half ^ 8)⟩,
       ⟨((-115 : Dyadic) * half ^ 9),
        ((27 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((157 : Dyadic) * half ^ 9),
        ((119 : Dyadic) * half ^ 8)⟩,
       ⟨((5 : Dyadic) * half ^ 5),
        ((-91 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word25Step15 :
    word25Chunk15.foldl (fun acc a => a.applyPacked acc)
      word25State15 = word25State16 := by decide +kernel

private def word25Chunk16 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word25State17 : PackedMat2 :=
    ⟨⟨⟨((-391 : Dyadic) * half ^ 10),
        ((-329 : Dyadic) * half ^ 11)⟩,
       ⟨((149 : Dyadic) * half ^ 10),
        ((-321 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((313 : Dyadic) * half ^ 9),
        ((191 : Dyadic) * half ^ 11)⟩,
       ⟨((33 : Dyadic) * half ^ 7),
        ((-759 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-313 : Dyadic) * half ^ 9),
        ((-191 : Dyadic) * half ^ 11)⟩,
       ⟨((33 : Dyadic) * half ^ 7),
        ((-759 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-391 : Dyadic) * half ^ 10),
        ((-329 : Dyadic) * half ^ 11)⟩,
       ⟨((-149 : Dyadic) * half ^ 10),
        ((321 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word25Step16 :
    word25Chunk16.foldl (fun acc a => a.applyPacked acc)
      word25State16 = word25State17 := by decide +kernel

private def word25Chunk17 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word25State18 : PackedMat2 :=
    ⟨⟨⟨((-97 : Dyadic) * half ^ 10),
        ((-1351 : Dyadic) * half ^ 12)⟩,
       ⟨((-1187 : Dyadic) * half ^ 11),
        ((-393 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-199 : Dyadic) * half ^ 10),
        ((1769 : Dyadic) * half ^ 12)⟩,
       ⟨((-137 : Dyadic) * half ^ 11),
        ((179 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((137 : Dyadic) * half ^ 11),
        ((-179 : Dyadic) * half ^ 12)⟩,
       ⟨((199 : Dyadic) * half ^ 10),
        ((-1769 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1187 : Dyadic) * half ^ 11),
        ((-393 : Dyadic) * half ^ 12)⟩,
       ⟨((-97 : Dyadic) * half ^ 10),
        ((-1351 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word25Step17 :
    word25Chunk17.foldl (fun acc a => a.applyPacked acc)
      word25State17 = word25State18 := by decide +kernel

private def word25Chunk18 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word25State19 : PackedMat2 :=
    ⟨⟨⟨((-795 : Dyadic) * half ^ 12),
        ((471 : Dyadic) * half ^ 13)⟩,
       ⟨((-1399 : Dyadic) * half ^ 11),
        ((-1493 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-449 : Dyadic) * half ^ 12),
        ((-1209 : Dyadic) * half ^ 13)⟩,
       ⟨((905 : Dyadic) * half ^ 11),
        ((-2401 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-149 : Dyadic) * half ^ 10),
        ((2259 : Dyadic) * half ^ 13)⟩,
       ⟨((-1805 : Dyadic) * half ^ 12),
        ((1361 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((491 : Dyadic) * half ^ 11),
        ((2003 : Dyadic) * half ^ 13)⟩,
       ⟨((511 : Dyadic) * half ^ 12),
        ((3593 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word25Step18 :
    word25Chunk18.foldl (fun acc a => a.applyPacked acc)
      word25State18 = word25State19 := by decide +kernel

private def word25Chunk19 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word25State20 : PackedMat2 :=
    ⟨⟨⟨((1859 : Dyadic) * half ^ 12),
        ((139 : Dyadic) * half ^ 11)⟩,
       ⟨((-239 : Dyadic) * half ^ 12),
        ((-3763 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1907 : Dyadic) * half ^ 12),
        ((987 : Dyadic) * half ^ 13)⟩,
       ⟨((-13 : Dyadic) * half ^ 11),
        ((61 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((13 : Dyadic) * half ^ 11),
        ((-61 : Dyadic) * half ^ 8)⟩,
       ⟨((1907 : Dyadic) * half ^ 12),
        ((-987 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-239 : Dyadic) * half ^ 12),
        ((-3763 : Dyadic) * half ^ 13)⟩,
       ⟨((1859 : Dyadic) * half ^ 12),
        ((139 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word25Step19 :
    word25Chunk19.foldl (fun acc a => a.applyPacked acc)
      word25State19 = word25State20 := by decide +kernel

private def word25Chunk20 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word25State21 : PackedMat2 :=
    ⟨⟨⟨((2555 : Dyadic) * half ^ 14),
        ((4681 : Dyadic) * half ^ 13)⟩,
       ⟨((-869 : Dyadic) * half ^ 14),
        ((-1855 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((6345 : Dyadic) * half ^ 14),
        ((-917 : Dyadic) * half ^ 12)⟩,
       ⟨((3297 : Dyadic) * half ^ 14),
        ((-685 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-4353 : Dyadic) * half ^ 14),
        ((4821 : Dyadic) * half ^ 14)⟩,
       ⟨((-2983 : Dyadic) * half ^ 14),
        ((381 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-7507 : Dyadic) * half ^ 14),
        ((-843 : Dyadic) * half ^ 14)⟩,
       ⟨((-11217 : Dyadic) * half ^ 14),
        ((-107 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word25Step20 :
    word25Chunk20.foldl (fun acc a => a.applyPacked acc)
      word25State20 = word25State21 := by decide +kernel

private def word25Chunk21 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word25State22 : PackedMat2 :=
    ⟨⟨⟨((18051 : Dyadic) * half ^ 15),
        ((1343 : Dyadic) * half ^ 13)⟩,
       ⟨((13013 : Dyadic) * half ^ 15),
        ((-1807 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((3535 : Dyadic) * half ^ 15),
        ((-1405 : Dyadic) * half ^ 13)⟩,
       ⟨((-20619 : Dyadic) * half ^ 15),
        ((2599 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((3021 : Dyadic) * half ^ 15),
        ((4271 : Dyadic) * half ^ 14)⟩,
       ⟨((8219 : Dyadic) * half ^ 15),
        ((-12077 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((3565 : Dyadic) * half ^ 15),
        ((3883 : Dyadic) * half ^ 13)⟩,
       ⟨((7179 : Dyadic) * half ^ 15),
        ((2519 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word25Step21 :
    word25Chunk21.foldl (fun acc a => a.applyPacked acc)
      word25State21 = word25State22 := by decide +kernel

private def word25Chunk22 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word25State23 : PackedMat2 :=
    ⟨⟨⟨((-2861 : Dyadic) * half ^ 13),
        ((22457 : Dyadic) * half ^ 16)⟩,
       ⟨((4493 : Dyadic) * half ^ 14),
        ((12765 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-1817 : Dyadic) * half ^ 15),
        ((2743 : Dyadic) * half ^ 16)⟩,
       ⟨((-4659 : Dyadic) * half ^ 15),
        ((-31611 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-1817 : Dyadic) * half ^ 15),
        ((2743 : Dyadic) * half ^ 16)⟩,
       ⟨((4659 : Dyadic) * half ^ 15),
        ((31611 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((2861 : Dyadic) * half ^ 13),
        ((-22457 : Dyadic) * half ^ 16)⟩,
       ⟨((4493 : Dyadic) * half ^ 14),
        ((12765 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word25Step22 :
    word25Chunk22.foldl (fun acc a => a.applyPacked acc)
      word25State22 = word25State23 := by decide +kernel

private def word25Chunk23 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word25State24 : PackedMat2 :=
    ⟨⟨⟨((27905 : Dyadic) * half ^ 16),
        ((-29177 : Dyadic) * half ^ 17)⟩,
       ⟨((-991 : Dyadic) * half ^ 12),
        ((37587 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((25013 : Dyadic) * half ^ 16),
        ((25519 : Dyadic) * half ^ 17)⟩,
       ⟨((-14291 : Dyadic) * half ^ 15),
        ((-27005 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-14291 : Dyadic) * half ^ 15),
        ((-27005 : Dyadic) * half ^ 17)⟩,
       ⟨((25013 : Dyadic) * half ^ 16),
        ((25519 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((991 : Dyadic) * half ^ 12),
        ((-37587 : Dyadic) * half ^ 17)⟩,
       ⟨((-27905 : Dyadic) * half ^ 16),
        ((29177 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word25Step23 :
    word25Chunk23.foldl (fun acc a => a.applyPacked acc)
      word25State23 = word25State24 := by decide +kernel

private def word25Chunk24 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word25State25 : PackedMat2 :=
    ⟨⟨⟨((-20227 : Dyadic) * half ^ 15),
        ((-58219 : Dyadic) * half ^ 18)⟩,
       ⟨((-26743 : Dyadic) * half ^ 17),
        ((57481 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((17433 : Dyadic) * half ^ 16),
        ((-15225 : Dyadic) * half ^ 18)⟩,
       ⟨((-66761 : Dyadic) * half ^ 17),
        ((39579 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-13701 : Dyadic) * half ^ 16),
        ((101627 : Dyadic) * half ^ 18)⟩,
       ⟨((-12177 : Dyadic) * half ^ 17),
        ((31895 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((28925 : Dyadic) * half ^ 16),
        ((54165 : Dyadic) * half ^ 18)⟩,
       ⟨((-369 : Dyadic) * half ^ 17),
        ((-107651 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word25Step24 :
    word25Chunk24.foldl (fun acc a => a.applyPacked acc)
      word25State24 = word25State25 := by decide +kernel

private def word25Chunk25 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word25State26 : PackedMat2 :=
    ⟨⟨⟨((-42357 : Dyadic) * half ^ 18),
        ((-127623 : Dyadic) * half ^ 18)⟩,
       ⟨((-77203 : Dyadic) * half ^ 18),
        ((77527 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((114173 : Dyadic) * half ^ 18),
        ((2619 : Dyadic) * half ^ 16)⟩,
       ⟨((53357 : Dyadic) * half ^ 18),
        ((-5777 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-539 : Dyadic) * half ^ 17),
        ((83765 : Dyadic) * half ^ 18)⟩,
       ⟨((11015 : Dyadic) * half ^ 17),
        ((3801 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((3131 : Dyadic) * half ^ 14),
        ((14945 : Dyadic) * half ^ 16)⟩,
       ⟨((102575 : Dyadic) * half ^ 17),
        ((-17423 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word25Step25 :
    word25Chunk25.foldl (fun acc a => a.applyPacked acc)
      word25State25 = word25State26 := by decide +kernel

private def word25Chunk26 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word25State27 : PackedMat2 :=
    ⟨⟨⟨((-176965 : Dyadic) * half ^ 19),
        ((-203649 : Dyadic) * half ^ 19)⟩,
       ⟨((90667 : Dyadic) * half ^ 19),
        ((-117617 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-82501 : Dyadic) * half ^ 19),
        ((65947 : Dyadic) * half ^ 19)⟩,
       ⟨((-114085 : Dyadic) * half ^ 19),
        ((10157 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((82501 : Dyadic) * half ^ 19),
        ((-65947 : Dyadic) * half ^ 19)⟩,
       ⟨((-114085 : Dyadic) * half ^ 19),
        ((10157 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-176965 : Dyadic) * half ^ 19),
        ((-203649 : Dyadic) * half ^ 19)⟩,
       ⟨((-90667 : Dyadic) * half ^ 19),
        ((117617 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word25Step26 :
    word25Chunk26.foldl (fun acc a => a.applyPacked acc)
      word25State26 = word25State27 := by decide +kernel

private def word25Chunk27 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word25State28 : PackedMat2 :=
    ⟨⟨⟨((-172595 : Dyadic) * half ^ 20),
        ((-168493 : Dyadic) * half ^ 20)⟩,
       ⟨((-320371 : Dyadic) * half ^ 20),
        ((-214153 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-517015 : Dyadic) * half ^ 20),
        ((176461 : Dyadic) * half ^ 20)⟩,
       ⟨((-306931 : Dyadic) * half ^ 20),
        ((122283 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((421027 : Dyadic) * half ^ 20),
        ((-411973 : Dyadic) * half ^ 20)⟩,
       ⟨((-68105 : Dyadic) * half ^ 20),
        ((-52521 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((596799 : Dyadic) * half ^ 20),
        ((246483 : Dyadic) * half ^ 20)⟩,
       ⟨((-259813 : Dyadic) * half ^ 20),
        ((-2309 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word25Step27 :
    word25Chunk27.foldl (fun acc a => a.applyPacked acc)
      word25State27 = word25State28 := by decide +kernel

private def word25Chunk28 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word25State29 : PackedMat2 :=
    ⟨⟨⟨((-190459 : Dyadic) * half ^ 20),
        ((29593 : Dyadic) * half ^ 19)⟩,
       ⟨((-41469 : Dyadic) * half ^ 18),
        ((-270665 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((117689 : Dyadic) * half ^ 19),
        ((-203095 : Dyadic) * half ^ 20)⟩,
       ⟨((-79521 : Dyadic) * half ^ 20),
        ((96569 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((589371 : Dyadic) * half ^ 20),
        ((-314899 : Dyadic) * half ^ 21)⟩,
       ⟨((183181 : Dyadic) * half ^ 20),
        ((155857 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((150129 : Dyadic) * half ^ 18),
        ((-24583 : Dyadic) * half ^ 21)⟩,
       ⟨((15067 : Dyadic) * half ^ 15),
        ((356335 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word25Step28 :
    word25Chunk28.foldl (fun acc a => a.applyPacked acc)
      word25State28 = word25State29 := by decide +kernel

private def word25Chunk29 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word25State30 : PackedMat2 :=
    ⟨⟨⟨((1192505 : Dyadic) * half ^ 21),
        ((168999 : Dyadic) * half ^ 22)⟩,
       ⟨((-535833 : Dyadic) * half ^ 21),
        ((-728751 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-46085 : Dyadic) * half ^ 18),
        ((1343993 : Dyadic) * half ^ 22)⟩,
       ⟨((-29191 : Dyadic) * half ^ 20),
        ((1653209 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-46085 : Dyadic) * half ^ 18),
        ((1343993 : Dyadic) * half ^ 22)⟩,
       ⟨((29191 : Dyadic) * half ^ 20),
        ((-1653209 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-1192505 : Dyadic) * half ^ 21),
        ((-168999 : Dyadic) * half ^ 22)⟩,
       ⟨((-535833 : Dyadic) * half ^ 21),
        ((-728751 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word25Step29 :
    word25Chunk29.foldl (fun acc a => a.applyPacked acc)
      word25State29 = word25State30 := by decide +kernel

private def word25Chunk30 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word25State31 : PackedMat2 :=
    ⟨⟨⟨((400013 : Dyadic) * half ^ 20),
        ((389277 : Dyadic) * half ^ 20)⟩,
       ⟨((-2041299 : Dyadic) * half ^ 22),
        ((326019 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-1607579 : Dyadic) * half ^ 22),
        ((41757 : Dyadic) * half ^ 20)⟩,
       ⟨((548601 : Dyadic) * half ^ 21),
        ((-812921 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1607579 : Dyadic) * half ^ 22),
        ((-41757 : Dyadic) * half ^ 20)⟩,
       ⟨((548601 : Dyadic) * half ^ 21),
        ((-812921 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((400013 : Dyadic) * half ^ 20),
        ((389277 : Dyadic) * half ^ 20)⟩,
       ⟨((2041299 : Dyadic) * half ^ 22),
        ((-326019 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word25Step30 :
    word25Chunk30.foldl (fun acc a => a.applyPacked acc)
      word25State30 = word25State31 := by decide +kernel

private def word25Chunk31 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word25State32 : PackedMat2 :=
    ⟨⟨⟨((-726347 : Dyadic) * half ^ 23),
        ((619131 : Dyadic) * half ^ 22)⟩,
       ⟨((1117243 : Dyadic) * half ^ 23),
        ((1280437 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-3908055 : Dyadic) * half ^ 23),
        ((-746421 : Dyadic) * half ^ 23)⟩,
       ⟨((5886349 : Dyadic) * half ^ 23),
        ((-828827 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((98453 : Dyadic) * half ^ 19),
        ((-989147 : Dyadic) * half ^ 23)⟩,
       ⟨((-41203 : Dyadic) * half ^ 22),
        ((2448601 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((118723 : Dyadic) * half ^ 18),
        ((24431 : Dyadic) * half ^ 20)⟩,
       ⟨((-330653 : Dyadic) * half ^ 21),
        ((-921795 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word25Step31 :
    word25Chunk31.foldl (fun acc a => a.applyPacked acc)
      word25State31 = word25State32 := by decide +kernel

private def word25Chunk32 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word25State33 : PackedMat2 :=
    ⟨⟨⟨((-215967 : Dyadic) * half ^ 24),
        ((-1149037 : Dyadic) * half ^ 23)⟩,
       ⟨((4477807 : Dyadic) * half ^ 24),
        ((-2541697 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-11178327 : Dyadic) * half ^ 24),
        ((-818669 : Dyadic) * half ^ 22)⟩,
       ⟨((-4243097 : Dyadic) * half ^ 24),
        ((6061723 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-11178327 : Dyadic) * half ^ 24),
        ((-818669 : Dyadic) * half ^ 22)⟩,
       ⟨((4243097 : Dyadic) * half ^ 24),
        ((-6061723 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((215967 : Dyadic) * half ^ 24),
        ((1149037 : Dyadic) * half ^ 23)⟩,
       ⟨((4477807 : Dyadic) * half ^ 24),
        ((-2541697 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word25Step32 :
    word25Chunk32.foldl (fun acc a => a.applyPacked acc)
      word25State32 = word25State33 := by decide +kernel

private def word25Chunk33 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word25State34 : PackedMat2 :=
    ⟨⟨⟨((-8154699 : Dyadic) * half ^ 25),
        ((-4330745 : Dyadic) * half ^ 24)⟩,
       ⟨((-2450381 : Dyadic) * half ^ 25),
        ((-16548881 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-13145691 : Dyadic) * half ^ 25),
        ((374633 : Dyadic) * half ^ 21)⟩,
       ⟨((9315707 : Dyadic) * half ^ 25),
        ((-3476489 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-2517639 : Dyadic) * half ^ 25),
        ((119687 : Dyadic) * half ^ 21)⟩,
       ⟨((-9470617 : Dyadic) * half ^ 25),
        ((11230699 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-25210371 : Dyadic) * half ^ 25),
        ((-1325635 : Dyadic) * half ^ 23)⟩,
       ⟨((7887391 : Dyadic) * half ^ 25),
        ((-2852159 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word25Step33 :
    word25Chunk33.foldl (fun acc a => a.applyPacked acc)
      word25State33 = word25State34 := by decide +kernel

private def word25Chunk34 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word25State35 : PackedMat2 :=
    ⟨⟨⟨((-431727 : Dyadic) * half ^ 24),
        ((1200027 : Dyadic) * half ^ 25)⟩,
       ⟨((-15968377 : Dyadic) * half ^ 25),
        ((-1823545 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-2741075 : Dyadic) * half ^ 25),
        ((-4582673 : Dyadic) * half ^ 24)⟩,
       ⟨((-551509 : Dyadic) * half ^ 21),
        ((7964679 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-2741075 : Dyadic) * half ^ 25),
        ((-4582673 : Dyadic) * half ^ 24)⟩,
       ⟨((551509 : Dyadic) * half ^ 21),
        ((-7964679 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((431727 : Dyadic) * half ^ 24),
        ((-1200027 : Dyadic) * half ^ 25)⟩,
       ⟨((-15968377 : Dyadic) * half ^ 25),
        ((-1823545 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word25Step34 :
    word25Chunk34.foldl (fun acc a => a.applyPacked acc)
      word25State34 = word25State35 := by decide +kernel

private def word25Chunk35 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word25State36 : PackedMat2 :=
    ⟨⟨⟨((22584963 : Dyadic) * half ^ 26),
        ((8962537 : Dyadic) * half ^ 27)⟩,
       ⟨((8917457 : Dyadic) * half ^ 25),
        ((-31702133 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-12666031 : Dyadic) * half ^ 26),
        ((-9845009 : Dyadic) * half ^ 27)⟩,
       ⟨((-195081 : Dyadic) * half ^ 22),
        ((-76342987 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-33248989 : Dyadic) * half ^ 26),
        ((9544735 : Dyadic) * half ^ 27)⟩,
       ⟨((-21546999 : Dyadic) * half ^ 25),
        ((-15787327 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((20332335 : Dyadic) * half ^ 26),
        ((4750049 : Dyadic) * half ^ 27)⟩,
       ⟨((5684899 : Dyadic) * half ^ 25),
        ((-40419877 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word25Step35 :
    word25Chunk35.foldl (fun acc a => a.applyPacked acc)
      word25State35 = word25State36 := by decide +kernel

private def word25Chunk36 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word25State37 : PackedMat2 :=
    ⟨⟨⟨((-5751081 : Dyadic) * half ^ 27),
        ((76607523 : Dyadic) * half ^ 27)⟩,
       ⟨((3548861 : Dyadic) * half ^ 27),
        ((27238687 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((11111201 : Dyadic) * half ^ 27),
        ((2413599 : Dyadic) * half ^ 25)⟩,
       ⟨((-66424055 : Dyadic) * half ^ 27),
        ((-890633 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((66424055 : Dyadic) * half ^ 27),
        ((890633 : Dyadic) * half ^ 25)⟩,
       ⟨((-11111201 : Dyadic) * half ^ 27),
        ((-2413599 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((3548861 : Dyadic) * half ^ 27),
        ((27238687 : Dyadic) * half ^ 27)⟩,
       ⟨((-5751081 : Dyadic) * half ^ 27),
        ((76607523 : Dyadic) * half ^ 27)⟩⟩⟩
private lemma word25Step36 :
    word25Chunk36.foldl (fun acc a => a.applyPacked acc)
      word25State36 = word25State37 := by decide +kernel

private def word25Chunk37 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word25State38 : PackedMat2 :=
    ⟨⟨⟨((162883113 : Dyadic) * half ^ 28),
        ((1444465 : Dyadic) * half ^ 26)⟩,
       ⟨((42634429 : Dyadic) * half ^ 28),
        ((107812811 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((36364011 : Dyadic) * half ^ 28),
        ((2415463 : Dyadic) * half ^ 25)⟩,
       ⟨((107832347 : Dyadic) * half ^ 28),
        ((-57870769 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((36364011 : Dyadic) * half ^ 28),
        ((2415463 : Dyadic) * half ^ 25)⟩,
       ⟨((-107832347 : Dyadic) * half ^ 28),
        ((57870769 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-162883113 : Dyadic) * half ^ 28),
        ((-1444465 : Dyadic) * half ^ 26)⟩,
       ⟨((42634429 : Dyadic) * half ^ 28),
        ((107812811 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word25Step37 :
    word25Chunk37.foldl (fun acc a => a.applyPacked acc)
      word25State37 = word25State38 := by decide +kernel

private def word25Chunk38 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word25State39 : PackedMat2 :=
    ⟨⟨⟨((-57589505 : Dyadic) * half ^ 27),
        ((-89200497 : Dyadic) * half ^ 29)⟩,
       ⟨((68096605 : Dyadic) * half ^ 27),
        ((-71374359 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((17516533 : Dyadic) * half ^ 28),
        ((-57311445 : Dyadic) * half ^ 29)⟩,
       ⟨((1787635 : Dyadic) * half ^ 28),
        ((252051423 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((77340717 : Dyadic) * half ^ 27),
        ((-7864449 : Dyadic) * half ^ 28)⟩,
       ⟨((97369989 : Dyadic) * half ^ 28),
        ((2413021 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-8913069 : Dyadic) * half ^ 28),
        ((-62843055 : Dyadic) * half ^ 27)⟩,
       ⟨((20071857 : Dyadic) * half ^ 26),
        ((-2626775 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word25Step38 :
    word25Chunk38.foldl (fun acc a => a.applyPacked acc)
      word25State38 = word25State39 := by decide +kernel

private def word25Chunk39 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word25State40 : PackedMat2 :=
    ⟨⟨⟨((-14069817 : Dyadic) * half ^ 28),
        ((161254059 : Dyadic) * half ^ 30)⟩,
       ⟨((-314143115 : Dyadic) * half ^ 29),
        ((-54123383 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-77544703 : Dyadic) * half ^ 27),
        ((-107636721 : Dyadic) * half ^ 30)⟩,
       ⟨((228277897 : Dyadic) * half ^ 29),
        ((-200858203 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((46610741 : Dyadic) * half ^ 29),
        ((-538456709 : Dyadic) * half ^ 30)⟩,
       ⟨((77123731 : Dyadic) * half ^ 28),
        ((81900915 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-107688721 : Dyadic) * half ^ 29),
        ((-286003481 : Dyadic) * half ^ 30)⟩,
       ⟨((26782669 : Dyadic) * half ^ 28),
        ((-342282749 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word25Step39 :
    word25Chunk39.foldl (fun acc a => a.applyPacked acc)
      word25State39 = word25State40 := by decide +kernel

private def word25Chunk40 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word25State41 : PackedMat2 :=
    ⟨⟨⟨((496582211 : Dyadic) * half ^ 30),
        ((-11236997 : Dyadic) * half ^ 26)⟩,
       ⟨((493816281 : Dyadic) * half ^ 30),
        ((-5625549 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((20822935 : Dyadic) * half ^ 30),
        ((-257982633 : Dyadic) * half ^ 30)⟩,
       ⟨((-639138833 : Dyadic) * half ^ 30),
        ((-165481091 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-639138833 : Dyadic) * half ^ 30),
        ((-165481091 : Dyadic) * half ^ 30)⟩,
       ⟨((20822935 : Dyadic) * half ^ 30),
        ((-257982633 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-493816281 : Dyadic) * half ^ 30),
        ((5625549 : Dyadic) * half ^ 28)⟩,
       ⟨((-496582211 : Dyadic) * half ^ 30),
        ((11236997 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word25Step40 :
    word25Chunk40.foldl (fun acc a => a.applyPacked acc)
      word25State40 = word25State41 := by decide +kernel

private def word25Chunk41 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word25State42 : PackedMat2 :=
    ⟨⟨⟨((-1786827081 : Dyadic) * half ^ 31),
        ((19098011 : Dyadic) * half ^ 30)⟩,
       ⟨((-178705283 : Dyadic) * half ^ 31),
        ((79926857 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((31998075 : Dyadic) * half ^ 31),
        ((193986701 : Dyadic) * half ^ 29)⟩,
       ⟨((-260084167 : Dyadic) * half ^ 31),
        ((-221867539 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-554079265 : Dyadic) * half ^ 31),
        ((57021523 : Dyadic) * half ^ 30)⟩,
       ⟨((-997814343 : Dyadic) * half ^ 31),
        ((-146041121 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((118122879 : Dyadic) * half ^ 31),
        ((-491383091 : Dyadic) * half ^ 30)⟩,
       ⟨((-41730835 : Dyadic) * half ^ 31),
        ((-804060899 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word25Step41 :
    word25Chunk41.foldl (fun acc a => a.applyPacked acc)
      word25State41 = word25State42 := by decide +kernel

private def word25Chunk42 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word25State43 : PackedMat2 :=
    ⟨⟨⟨((257590747 : Dyadic) * half ^ 31),
        ((-1644886399 : Dyadic) * half ^ 32)⟩,
       ⟨((-829485721 : Dyadic) * half ^ 31),
        ((-916456065 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((408318123 : Dyadic) * half ^ 30),
        ((333792471 : Dyadic) * half ^ 32)⟩,
       ⟨((-549641021 : Dyadic) * half ^ 30),
        ((554058659 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-55066547 : Dyadic) * half ^ 30),
        ((119744893 : Dyadic) * half ^ 28)⟩,
       ⟨((-443925565 : Dyadic) * half ^ 31),
        ((70661449 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((364215167 : Dyadic) * half ^ 31),
        ((-271769117 : Dyadic) * half ^ 30)⟩,
       ⟨((-2501311 : Dyadic) * half ^ 22),
        ((-285947487 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word25Step42 :
    word25Chunk42.foldl (fun acc a => a.applyPacked acc)
      word25State42 = word25State43 := by decide +kernel

private def word25Chunk43 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word25State44 : PackedMat2 :=
    ⟨⟨⟨((834923303 : Dyadic) * half ^ 31),
        ((217938977 : Dyadic) * half ^ 31)⟩,
       ⟨((-292272729 : Dyadic) * half ^ 32),
        ((-298203639 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-1677709241 : Dyadic) * half ^ 32),
        ((680705863 : Dyadic) * half ^ 31)⟩,
       ⟨((-682234829 : Dyadic) * half ^ 30),
        ((-506383605 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1677709241 : Dyadic) * half ^ 32),
        ((-680705863 : Dyadic) * half ^ 31)⟩,
       ⟨((-682234829 : Dyadic) * half ^ 30),
        ((-506383605 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((834923303 : Dyadic) * half ^ 31),
        ((217938977 : Dyadic) * half ^ 31)⟩,
       ⟨((292272729 : Dyadic) * half ^ 32),
        ((298203639 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word25Step43 :
    word25Chunk43.foldl (fun acc a => a.applyPacked acc)
      word25State43 = word25State44 := by decide +kernel

private def word25Chunk44 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word25State45 : PackedMat2 :=
    ⟨⟨⟨((1009528379 : Dyadic) * half ^ 32),
        ((125859211 : Dyadic) * half ^ 34)⟩,
       ⟨((2344827381 : Dyadic) * half ^ 33),
        ((1338440525 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((1403073023 : Dyadic) * half ^ 31),
        ((-3720225149 : Dyadic) * half ^ 34)⟩,
       ⟨((-3722761683 : Dyadic) * half ^ 33),
        ((-4697174515 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((3722761683 : Dyadic) * half ^ 33),
        ((4697174515 : Dyadic) * half ^ 34)⟩,
       ⟨((-1403073023 : Dyadic) * half ^ 31),
        ((3720225149 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((2344827381 : Dyadic) * half ^ 33),
        ((1338440525 : Dyadic) * half ^ 34)⟩,
       ⟨((1009528379 : Dyadic) * half ^ 32),
        ((125859211 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word25Step44 :
    word25Chunk44.foldl (fun acc a => a.applyPacked acc)
      word25State44 = word25State45 := by decide +kernel

private def word25Chunk45 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word25State46 : PackedMat2 :=
    ⟨⟨⟨((-5941729853 : Dyadic) * half ^ 34),
        ((-499375381 : Dyadic) * half ^ 33)⟩,
       ⟨((8969789375 : Dyadic) * half ^ 34),
        ((136911103 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-2342290847 : Dyadic) * half ^ 34),
        ((7291659087 : Dyadic) * half ^ 34)⟩,
       ⟨((-1103939181 : Dyadic) * half ^ 34),
        ((-5645803863 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((205731903 : Dyadic) * half ^ 31),
        ((-861557507 : Dyadic) * half ^ 33)⟩,
       ⟨((6468731475 : Dyadic) * half ^ 33),
        ((-619175833 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((225553175 : Dyadic) * half ^ 33),
        ((-1514029761 : Dyadic) * half ^ 34)⟩,
       ⟨((773197587 : Dyadic) * half ^ 33),
        ((3727879807 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word25Step45 :
    word25Chunk45.foldl (fun acc a => a.applyPacked acc)
      word25State45 = word25State46 := by decide +kernel

private def word25Chunk46 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word25State47 : PackedMat2 :=
    ⟨⟨⟨((-6916745543 : Dyadic) * half ^ 35),
        ((287005823 : Dyadic) * half ^ 35)⟩,
       ⟨((-14258686397 : Dyadic) * half ^ 35),
        ((2806719225 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((22325422831 : Dyadic) * half ^ 35),
        ((-1266280295 : Dyadic) * half ^ 35)⟩,
       ⟨((9377292933 : Dyadic) * half ^ 35),
        ((2940498087 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-10495712053 : Dyadic) * half ^ 35),
        ((-7925678941 : Dyadic) * half ^ 34)⟩,
       ⟨((13028272643 : Dyadic) * half ^ 35),
        ((-6474064949 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((5900444273 : Dyadic) * half ^ 35),
        ((-5293857985 : Dyadic) * half ^ 34)⟩,
       ⟨((-5326432627 : Dyadic) * half ^ 35),
        ((3670970427 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word25Step46 :
    word25Chunk46.foldl (fun acc a => a.applyPacked acc)
      word25State46 = word25State47 := by decide +kernel

private def word25Chunk47 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word25State48 : PackedMat2 :=
    ⟨⟨⟨((378281109 : Dyadic) * half ^ 30),
        ((-768191645 : Dyadic) * half ^ 36)⟩,
       ⟨((6658888547 : Dyadic) * half ^ 34),
        ((-15237960869 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((1174416437 : Dyadic) * half ^ 35),
        ((4949992033 : Dyadic) * half ^ 36)⟩,
       ⟨((26383076535 : Dyadic) * half ^ 35),
        ((7824006815 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-1437007391 : Dyadic) * half ^ 35),
        ((-12604330049 : Dyadic) * half ^ 35)⟩,
       ⟨((-49898433 : Dyadic) * half ^ 28),
        ((-6889373243 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1808721153 : Dyadic) * half ^ 33),
        ((606390803 : Dyadic) * half ^ 35)⟩,
       ⟨((-8003076257 : Dyadic) * half ^ 35),
        ((12711386291 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word25Step47 :
    word25Chunk47.foldl (fun acc a => a.applyPacked acc)
      word25State47 = word25State48 := by decide +kernel

private def word25Chunk48 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word25State49 : PackedMat2 :=
    ⟨⟨⟨((11048917881 : Dyadic) * half ^ 36),
        ((-50353718883 : Dyadic) * half ^ 37)⟩,
       ⟨((-24034523779 : Dyadic) * half ^ 36),
        ((22731467597 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((177143257 : Dyadic) * half ^ 33),
        ((-39121844727 : Dyadic) * half ^ 37)⟩,
       ⟨((16896807979 : Dyadic) * half ^ 35),
        ((34270836031 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-177143257 : Dyadic) * half ^ 33),
        ((39121844727 : Dyadic) * half ^ 37)⟩,
       ⟨((16896807979 : Dyadic) * half ^ 35),
        ((34270836031 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((11048917881 : Dyadic) * half ^ 36),
        ((-50353718883 : Dyadic) * half ^ 37)⟩,
       ⟨((24034523779 : Dyadic) * half ^ 36),
        ((-22731467597 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word25Step48 :
    word25Chunk48.foldl (fun acc a => a.applyPacked acc)
      word25State48 = word25State49 := by decide +kernel

private def word25Chunk49 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word25State50 : PackedMat2 :=
    ⟨⟨⟨((-12521299941 : Dyadic) * half ^ 37),
        ((-120341628409 : Dyadic) * half ^ 38)⟩,
       ⟨((11069920643 : Dyadic) * half ^ 36),
        ((-23583848219 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-58836498029 : Dyadic) * half ^ 37),
        ((-15450451147 : Dyadic) * half ^ 38)⟩,
       ⟨((41478010137 : Dyadic) * half ^ 36),
        ((-22828257677 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-41478010137 : Dyadic) * half ^ 36),
        ((22828257677 : Dyadic) * half ^ 38)⟩,
       ⟨((58836498029 : Dyadic) * half ^ 37),
        ((15450451147 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((11069920643 : Dyadic) * half ^ 36),
        ((-23583848219 : Dyadic) * half ^ 38)⟩,
       ⟨((-12521299941 : Dyadic) * half ^ 37),
        ((-120341628409 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word25Step49 :
    word25Chunk49.foldl (fun acc a => a.applyPacked acc)
      word25State49 = word25State50 := by decide +kernel

private def word25Chunk50 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word25State51 : PackedMat2 :=
    ⟨⟨⟨((-9714519257 : Dyadic) * half ^ 36),
        ((21286203289 : Dyadic) * half ^ 37)⟩,
       ⟨((-55156391403 : Dyadic) * half ^ 37),
        ((27326639729 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-46196678647 : Dyadic) * half ^ 37),
        ((-46947634067 : Dyadic) * half ^ 38)⟩,
       ⟨((-104655381405 : Dyadic) * half ^ 37),
        ((-790953113 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-48529540293 : Dyadic) * half ^ 38),
        ((-37713015013 : Dyadic) * half ^ 36)⟩,
       ⟨((-45365727841 : Dyadic) * half ^ 38),
        ((29229351379 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-69899046307 : Dyadic) * half ^ 38),
        ((74585429917 : Dyadic) * half ^ 38)⟩,
       ⟨((-15245766849 : Dyadic) * half ^ 38),
        ((-35727352889 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word25Step50 :
    word25Chunk50.foldl (fun acc a => a.applyPacked acc)
      word25State50 = word25State51 := by decide +kernel

private def word25Chunk51 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word25State52 : PackedMat2 :=
    ⟨⟨⟨((-71116499229 : Dyadic) * half ^ 37),
        ((13842954663 : Dyadic) * half ^ 37)⟩,
       ⟨((34196177245 : Dyadic) * half ^ 37),
        ((-19664834371 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-20327857291 : Dyadic) * half ^ 36),
        ((123328829377 : Dyadic) * half ^ 39)⟩,
       ⟨((-81168295139 : Dyadic) * half ^ 38),
        ((-118572574803 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((113816320229 : Dyadic) * half ^ 39),
        ((162479724303 : Dyadic) * half ^ 39)⟩,
       ⟨((-360473978983 : Dyadic) * half ^ 39),
        ((143134025 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((35706984281 : Dyadic) * half ^ 39),
        ((-576880031 : Dyadic) * half ^ 32)⟩,
       ⟨((75036653023 : Dyadic) * half ^ 39),
        ((-52656338237 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word25Step51 :
    word25Chunk51.foldl (fun acc a => a.applyPacked acc)
      word25State51 = word25State52 := by decide +kernel

private def word25Chunk52 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word25State53 : PackedMat2 :=
    ⟨⟨⟨((296642526213 : Dyadic) * half ^ 40),
        ((46668268323 : Dyadic) * half ^ 37)⟩,
       ⟨((-55325912457 : Dyadic) * half ^ 40),
        ((-20694300833 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((301332928161 : Dyadic) * half ^ 40),
        ((-18706480965 : Dyadic) * half ^ 40)⟩,
       ⟨((180039791109 : Dyadic) * half ^ 40),
        ((-596553277921 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((180039791109 : Dyadic) * half ^ 40),
        ((-596553277921 : Dyadic) * half ^ 40)⟩,
       ⟨((301332928161 : Dyadic) * half ^ 40),
        ((-18706480965 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((55325912457 : Dyadic) * half ^ 40),
        ((20694300833 : Dyadic) * half ^ 39)⟩,
       ⟨((-296642526213 : Dyadic) * half ^ 40),
        ((-46668268323 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word25Step52 :
    word25Chunk52.foldl (fun acc a => a.applyPacked acc)
      word25State52 = word25State53 := by decide +kernel

private def word25Chunk53 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word25State54 : PackedMat2 :=
    ⟨⟨⟨((1417277964511 : Dyadic) * half ^ 41),
        ((24336192061 : Dyadic) * half ^ 39)⟩,
       ⟨((-363981474075 : Dyadic) * half ^ 41),
        ((257373665601 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((114504791879 : Dyadic) * half ^ 41),
        ((15914758015 : Dyadic) * half ^ 35)⟩,
       ⟨((-477038879431 : Dyadic) * half ^ 41),
        ((337317529479 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-1355862042439 : Dyadic) * half ^ 41),
        ((2832297559 : Dyadic) * half ^ 35)⟩,
       ⟨((-681226983481 : Dyadic) * half ^ 41),
        ((-295771835655 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((354718433845 : Dyadic) * half ^ 41),
        ((263324122609 : Dyadic) * half ^ 40)⟩,
       ⟨((-160028897357 : Dyadic) * half ^ 41),
        ((890629719293 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word25Step53 :
    word25Chunk53.foldl (fun acc a => a.applyPacked acc)
      word25State53 = word25State54 := by decide +kernel

private def word25Chunk54 : List Letter := [.s, .t, .h]
private def word25State55 : PackedMat2 :=
    ⟨⟨⟨((278972320301 : Dyadic) * half ^ 39),
        ((765891378195 : Dyadic) * half ^ 41)⟩,
       ⟨((-39971931939 : Dyadic) * half ^ 40),
        ((28264351339 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((230299936179 : Dyadic) * half ^ 39),
        ((-162846646579 : Dyadic) * half ^ 39)⟩,
       ⟨((74336399385 : Dyadic) * half ^ 38),
        ((-420510176753 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-230299936179 : Dyadic) * half ^ 39),
        ((162846646579 : Dyadic) * half ^ 39)⟩,
       ⟨((74336399385 : Dyadic) * half ^ 38),
        ((-420510176753 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((278972320301 : Dyadic) * half ^ 39),
        ((765891378195 : Dyadic) * half ^ 41)⟩,
       ⟨((39971931939 : Dyadic) * half ^ 40),
        ((-28264351339 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word25Step54 :
    word25Chunk54.foldl (fun acc a => a.applyPacked acc)
      word25State54 = word25State55 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word25_check : check word25 25 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word25 = word25State55.toMatrix := by
    unfold evalRingPacked
    change ((
      word25Chunk0 ++ word25Chunk1 ++ word25Chunk2 ++ word25Chunk3 ++
      word25Chunk4 ++ word25Chunk5 ++ word25Chunk6 ++ word25Chunk7 ++
      word25Chunk8 ++ word25Chunk9 ++ word25Chunk10 ++ word25Chunk11 ++
      word25Chunk12 ++ word25Chunk13 ++ word25Chunk14 ++ word25Chunk15 ++
      word25Chunk16 ++ word25Chunk17 ++ word25Chunk18 ++ word25Chunk19 ++
      word25Chunk20 ++ word25Chunk21 ++ word25Chunk22 ++ word25Chunk23 ++
      word25Chunk24 ++ word25Chunk25 ++ word25Chunk26 ++ word25Chunk27 ++
      word25Chunk28 ++ word25Chunk29 ++ word25Chunk30 ++ word25Chunk31 ++
      word25Chunk32 ++ word25Chunk33 ++ word25Chunk34 ++ word25Chunk35 ++
      word25Chunk36 ++ word25Chunk37 ++ word25Chunk38 ++ word25Chunk39 ++
      word25Chunk40 ++ word25Chunk41 ++ word25Chunk42 ++ word25Chunk43 ++
      word25Chunk44 ++ word25Chunk45 ++ word25Chunk46 ++ word25Chunk47 ++
      word25Chunk48 ++ word25Chunk49 ++ word25Chunk50 ++ word25Chunk51 ++
      word25Chunk52 ++ word25Chunk53 ++ word25Chunk54
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word25Step0, word25Step1, word25Step2, word25Step3, word25Step4,
      word25Step5, word25Step6, word25Step7, word25Step8, word25Step9,
      word25Step10, word25Step11, word25Step12, word25Step13, word25Step14,
      word25Step15, word25Step16, word25Step17, word25Step18, word25Step19,
      word25Step20, word25Step21, word25Step22, word25Step23, word25Step24,
      word25Step25, word25Step26, word25Step27, word25Step28, word25Step29,
      word25Step30, word25Step31, word25Step32, word25Step33, word25Step34,
      word25Step35, word25Step36, word25Step37, word25Step38, word25Step39,
      word25Step40, word25Step41, word25Step42, word25Step43, word25Step44,
      word25Step45, word25Step46, word25Step47, word25Step48, word25Step49,
      word25Step50, word25Step51, word25Step52, word25Step53, word25Step54]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
