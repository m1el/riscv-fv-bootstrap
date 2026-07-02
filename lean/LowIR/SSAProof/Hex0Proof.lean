/-
  LowIR.SSAProof.Hex0Proof — Phases 2–6 of the hex0-on-SSA campaign
  (docs/RESUME-SSA-HEX0.md). Proves `hex0S_correct`: the SSA `hex0S` computes
  `Hex0.coreSpec`. The spec-side layer (pnibR bridges, boundedRun, commentSkip,
  decodeS unfolders, regionBytes, the geu/slt condition lemmas, the borrow
  Slice/Wf layer) imports VERBATIM from `LowIR.CtrlHex0Proof`; only the
  IL-facing pieces are rebuilt on the SSA `exec`.

  STATUS: in progress. Landed so far —
    • Phase 2: `pnibS_eff` — the value-producing nibble `ife` writes `pnibR c`
      into `dst` (all 5 leaves; frame follows separately from `exec_frame`).
  Remaining: prelude / read-char / cond-dispatch (Phase 2 tail), `skipCommentS_eff`
  (Phase 3), `body_step` (Phase 4), `main_loop` (Phase 5), assembly (Phase 6).
-/
import LowIR.SSAProof.ExecFacts
import LowIR.SSAProof.StrlenProof
import LowIR.SSALib
import LowIR.CtrlHex0Proof

namespace LowIR.SSA

open LowIR (Cond evalCond)
open Rv64i (Word Byte)
open LowIR.Ctrl.Hex0 (pnibR pnibR_nibble pnibR_eq_255_iff pnibR_lt_16 hexbyte_val
  geuL_true geuL_false slt_true slt_false tn regionBytes boundedRun commentSkip)

variable (env : Env) (sl : Word)

/-! ### Guard evaluation for the pnib byte comparisons (byte vs constant). -/

/-- `geu (byte) (const)` : true iff `const ≤ byte`. -/
theorem geuR_true (c : Byte) (m : Nat) (hm : (BitVec.ofNat 64 m).toNat = m) (h : m ≤ c.toNat) :
    evalCond .geu (c.setWidth 64) (BitVec.ofNat 64 m) = true :=
  LowIR.Ctrl.Strtoull2.geu_true hm h

theorem geuR_false (c : Byte) (m : Nat) (hm : (BitVec.ofNat 64 m).toNat = m) (h : c.toNat < m) :
    evalCond .geu (c.setWidth 64) (BitVec.ofNat 64 m) = false :=
  LowIR.Ctrl.Strtoull2.geu_false hm h

/-! ### `pnibS_eff` — the nibble decode `ife` writes `pnibR c` into `dst`.

    Every guard reads the entry state `s` (the nested `ife`s have no writes
    before the leaf `sub`), so `s.rget src`/consts suffice. The frame (all regs
    outside `{dst,t1,t2}` preserved) follows separately from `exec_frame`. -/

theorem pnibS_eff (s : St) (dst t1 t2 src : Reg) (c : Byte)
    (hsrc : s.rget src = c.setWidth 64)
    (h17 : s.rget 17 = 55) (h20 : s.rget 20 = 48) (h21 : s.rget 21 = 57)
    (h22 : s.rget 22 = 65) (h23 : s.rget 23 = 70)
    (hd0 : dst ≠ 0) (ht1 : t1 ≠ 0) (ht2 : t2 ≠ 0) :
    ∃ s', exec env sl 6 (Lib.pnibS dst t1 t2 src) s = some (s', .normal)
      ∧ s'.rget dst = pnibR c ∧ s'.mem = s.mem := by
  have c48 := LowIR.Ctrl.Hex0.c48
  have c57 := LowIR.Ctrl.Hex0.c57
  have c65 := LowIR.Ctrl.Hex0.c65
  have c70 := LowIR.Ctrl.Hex0.c70
  -- guard equalities (each reads the entry state `s`)
  have G1 (h : 48 ≤ c.toNat) : evalCond .geu (s.rget src) (s.rget 20) = true := by
    rw [hsrc, h20]; exact geuR_true c 48 c48 h
  have G1f (h : c.toNat < 48) : evalCond .geu (s.rget src) (s.rget 20) = false := by
    rw [hsrc, h20]; exact geuR_false c 48 c48 h
  have G2 (h : c.toNat ≤ 57) : evalCond .geu (s.rget 21) (s.rget src) = true := by
    rw [hsrc, h21]; exact geuL_true c 57 c57 h
  have G2f (h : 57 < c.toNat) : evalCond .geu (s.rget 21) (s.rget src) = false := by
    rw [hsrc, h21]; exact geuL_false c 57 c57 h
  have G3 (h : 65 ≤ c.toNat) : evalCond .geu (s.rget src) (s.rget 22) = true := by
    rw [hsrc, h22]; exact geuR_true c 65 c65 h
  have G3f (h : c.toNat < 65) : evalCond .geu (s.rget src) (s.rget 22) = false := by
    rw [hsrc, h22]; exact geuR_false c 65 c65 h
  have G4 (h : c.toNat ≤ 70) : evalCond .geu (s.rget 23) (s.rget src) = true := by
    rw [hsrc, h23]; exact geuL_true c 70 c70 h
  have G4f (h : 70 < c.toNat) : evalCond .geu (s.rget 23) (s.rget src) = false := by
    rw [hsrc, h23]; exact geuL_false c 70 c70 h
  unfold Lib.pnibS
  by_cases hg1 : 48 ≤ c.toNat
  · by_cases hg2 : c.toNat ≤ 57
    · -- '0'..'9': leaf A, dst := c - 48
      have hval : pnibR c = c.setWidth 64 - 48 := by unfold pnibR; rw [if_pos ⟨hg1, hg2⟩]
      have hsub : exec env sl 3 (.sub t1 src 20) s = some (s.rset t1 (c.setWidth 64 - 48), .normal) := by
        rw [show (3:Nat) = 2+1 from rfl, exec_sub, hsrc, h20]
      have hA : exec env sl 4 (.seq (.sub t1 src 20) (.brk 1 [.reg t1])) s
          = some (s.rset t1 (c.setWidth 64 - 48), .brk 1 [c.setWidth 64 - 48]) := by
        rw [show (4:Nat) = 3+1 from rfl, exec_seq_normal (h := hsub), exec_brk]
        simp [rget_rset_eq _ t1 _ ht1]
      refine ⟨(s.rset t1 (c.setWidth 64 - 48)).rset dst (c.setWidth 64 - 48), ?_, ?_, by simp⟩
      · rw [exec_ife_then (hc := G1 hg1), exec_ife_then (hc := G2 hg2), hA,
            catch0_brkS, catch0_brk0 _ _ _ (by rfl)]; rfl
      · rw [hval]; simp [rget_rset_eq _ dst _ hd0]
    · -- c > 57
      by_cases hg3 : 65 ≤ c.toNat
      · by_cases hg4 : c.toNat ≤ 70
        · -- 'A'..'F': leaf sub t2, dst := c - 55
          have hval : pnibR c = c.setWidth 64 - 55 := by
            unfold pnibR; rw [if_neg (by omega), if_pos ⟨hg3, hg4⟩]
          have hsub : exec env sl 1 (.sub t2 src 17) s = some (s.rset t2 (c.setWidth 64 - 55), .normal) := by
            rw [show (1:Nat) = 0+1 from rfl, exec_sub, hsrc, h17]
          have hA : exec env sl 2 (.seq (.sub t2 src 17) (.brk 3 [.reg t2])) s
              = some (s.rset t2 (c.setWidth 64 - 55), .brk 3 [c.setWidth 64 - 55]) := by
            rw [show (2:Nat) = 1+1 from rfl, exec_seq_normal (h := hsub), exec_brk]
            simp [rget_rset_eq _ t2 _ ht2]
          refine ⟨(s.rset t2 (c.setWidth 64 - 55)).rset dst (c.setWidth 64 - 55), ?_, ?_, by simp⟩
          · rw [exec_ife_then (hc := G1 hg1), exec_ife_else (hc := G2f (by omega)),
                exec_ife_then (hc := G3 hg3), exec_ife_then (hc := G4 hg4), hA,
                catch0_brkS, catch0_brkS, catch0_brkS, catch0_brk0 _ _ _ (by rfl)]; rfl
          · rw [hval]; simp [rget_rset_eq _ dst _ hd0]
        · -- c > 70: brk 3 [255], dst := 255
          have hval : pnibR c = 255 := by unfold pnibR; rw [if_neg (by omega), if_neg (by omega)]
          refine ⟨s.rset dst 255, ?_, ?_, by simp⟩
          · rw [exec_ife_then (hc := G1 hg1), exec_ife_else (hc := G2f (by omega)),
                exec_ife_then (hc := G3 hg3), exec_ife_else (hc := G4f (by omega)), exec_brk,
                catch0_brkS, catch0_brkS, catch0_brkS, catch0_brk0 _ _ _ (by rfl)]; rfl
          · rw [hval]; simp [rget_rset_eq _ dst _ hd0]
      · -- 57 < c < 65: brk 2 [255], dst := 255
        have hval : pnibR c = 255 := by unfold pnibR; rw [if_neg (by omega), if_neg (by omega)]
        refine ⟨s.rset dst 255, ?_, ?_, by simp⟩
        · rw [exec_ife_then (hc := G1 hg1), exec_ife_else (hc := G2f (by omega)),
              exec_ife_else (hc := G3f (by omega)), exec_brk,
              catch0_brkS, catch0_brkS, catch0_brk0 _ _ _ (by rfl)]; rfl
        · rw [hval]; simp [rget_rset_eq _ dst _ hd0]
  · -- c < 48: ELSE brk 0 [255], dst := 255
    have hval : pnibR c = 255 := by unfold pnibR; rw [if_neg (by omega), if_neg (by omega)]
    refine ⟨s.rset dst 255, ?_, ?_, by simp⟩
    · rw [exec_ife_else (hc := G1f (by omega)), exec_brk, catch0_brk0 _ _ _ (by rfl)]; rfl
    · rw [hval]; simp [rget_rset_eq _ dst _ hd0]

/-! ### `lit` — a single constant load (`v < 2048`, so the 12-bit immediate
    sign-extends to `v`). -/

theorem signExtend_ofNat_small (v : Nat) (hv : v < 2048) :
    (BitVec.ofNat 12 v).signExtend 64 = BitVec.ofNat 64 v := by
  apply BitVec.eq_of_toNat_eq
  have hlt : (BitVec.ofNat 12 v).toNat = v := by rw [BitVec.toNat_ofNat]; omega
  have hmsb : (BitVec.ofNat 12 v).msb = false := by
    rw [BitVec.msb_eq_decide, hlt]; exact decide_eq_false (by omega)
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth, hmsb]
  simp only [Bool.false_eq_true, if_false, Nat.add_zero, hlt, BitVec.toNat_ofNat]

theorem exec_lit (fuel r v : Nat) (s : St) (hv : v < 2048) :
    exec env sl (fuel+1) (Lib.lit r v) s = some (s.rset r (BitVec.ofNat 64 v), .normal) := by
  unfold Lib.lit
  rw [exec_addi, rget_zero, signExtend_ofNat_small v hv, show (0 : Word) + BitVec.ofNat 64 v
        = BitVec.ofNat 64 v from by bv_omega]

/-! ### Char-class condition lemmas (`.ife .eq` / `.ife .geu` over registers).
    Ported from `CtrlHex0Proof`'s `ceq`/`weq`/`geu_ww`; the proofs are
    IL-independent (only `evalCond`/`BitVec`), retargeted at `Prog.St.rget`. -/

/-- `eq (char reg = b widened) (const reg = n)`: true iff `b.toNat = n`. -/
theorem ceqS_true {s : St} {b : Byte} {cr r : Reg} {k : Word} (n : Nat)
    (hc : s.rget cr = b.setWidth 64) (hr : s.rget r = k) (hk : k.toNat = n)
    (h : b.toNat = n) : evalCond .eq (s.rget cr) (s.rget r) = true := by
  rw [hc, hr]; simp only [evalCond, decide_eq_true_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega), hk]; exact h

theorem ceqS_false {s : St} {b : Byte} {cr r : Reg} {k : Word} (n : Nat)
    (hc : s.rget cr = b.setWidth 64) (hr : s.rget r = k) (hk : k.toNat = n)
    (h : b.toNat ≠ n) : evalCond .eq (s.rget cr) (s.rget r) = false := by
  rw [hc, hr]; simp only [evalCond, decide_eq_false_iff_not]
  intro hcc; apply h
  have := congrArg BitVec.toNat hcc
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := b.isLt; omega), hk] at this
  exact this

/-- Raw word-equality dispatch (compares two registers' contents). -/
theorem weqS_true {s : St} {a b : Reg} {x y : Word} (ha : s.rget a = x) (hb : s.rget b = y)
    (h : x = y) : evalCond .eq (s.rget a) (s.rget b) = true := by
  rw [ha, hb]; simp only [evalCond, decide_eq_true_eq]; exact h
theorem weqS_false {s : St} {a b : Reg} {x y : Word} (ha : s.rget a = x) (hb : s.rget b = y)
    (h : x ≠ y) : evalCond .eq (s.rget a) (s.rget b) = false := by
  rw [ha, hb]; simp only [evalCond, decide_eq_false_iff_not]; exact h

/-- Unsigned `≥` between two registers' word contents. -/
theorem geu_wwS_true {s : St} {a b : Reg} {x y : Word} (ha : s.rget a = x) (hb : s.rget b = y)
    (h : y.toNat ≤ x.toNat) : evalCond .geu (s.rget a) (s.rget b) = true := by
  rw [ha, hb]; simp only [evalCond]
  rw [show x.ult y = decide (x.toNat < y.toNat) from rfl]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]; omega
theorem geu_wwS_false {s : St} {a b : Reg} {x y : Word} (ha : s.rget a = x) (hb : s.rget b = y)
    (h : x.toNat < y.toNat) : evalCond .geu (s.rget a) (s.rget b) = false := by
  rw [ha, hb]; simp only [evalCond]
  rw [show x.ult y = decide (x.toNat < y.toNat) from rfl]
  simp only [Bool.not_eq_false', decide_eq_true_eq]; omega

/-! ### The constant/param register context (SSA analogue of Ctrl's `Regs`,
    minus the status/guard/`1` registers). Re-established across the loop by the
    generic frame theorem `exec_frame_rget` — NOT by a bespoke `Pres`/`transfer`
    (P2, the headline claim). -/

structure RegsS (s : St) (p L q cap : Word) : Prop where
  h10 : s.rget 10 = p
  h11 : s.rget 11 = L
  h12 : s.rget 12 = q
  h13 : s.rget 13 = cap
  h17 : s.rget 17 = 55
  h18 : s.rget 18 = 59
  h19 : s.rget 19 = 255
  h20 : s.rget 20 = 48
  h21 : s.rget 21 = 57
  h22 : s.rget 22 = 65
  h23 : s.rget 23 = 70
  h24 : s.rget 24 = 10
  h25 : s.rget 25 = 32
  h26 : s.rget 26 = 95
  h27 : s.rget 27 = 35

/-- `RegsS` transfers across any state agreeing on the 15 const/param registers. -/
theorem RegsS.of_agree {s s' : St} {p L q cap : Word} (hr : RegsS s p L q cap)
    (h : ∀ r, r ∈ ([10,11,12,13,17,18,19,20,21,22,23,24,25,26,27] : List Reg) →
      s'.rget r = s.rget r) : RegsS s' p L q cap where
  h10 := by rw [h 10 (by decide)]; exact hr.h10
  h11 := by rw [h 11 (by decide)]; exact hr.h11
  h12 := by rw [h 12 (by decide)]; exact hr.h12
  h13 := by rw [h 13 (by decide)]; exact hr.h13
  h17 := by rw [h 17 (by decide)]; exact hr.h17
  h18 := by rw [h 18 (by decide)]; exact hr.h18
  h19 := by rw [h 19 (by decide)]; exact hr.h19
  h20 := by rw [h 20 (by decide)]; exact hr.h20
  h21 := by rw [h 21 (by decide)]; exact hr.h21
  h22 := by rw [h 22 (by decide)]; exact hr.h22
  h23 := by rw [h 23 (by decide)]; exact hr.h23
  h24 := by rw [h 24 (by decide)]; exact hr.h24
  h25 := by rw [h 25 (by decide)]; exact hr.h25
  h26 := by rw [h 26 (by decide)]; exact hr.h26
  h27 := by rw [h 27 (by decide)]; exact hr.h27

/-- `RegsS` survives one execution of the loop body (none of the 15 registers is
    a def site of `hex0BodyS`; frame theorem). -/
theorem RegsS.frame {s s' : St} {p L q cap : Word} {f : Nat} {oc : Outcome}
    (hr : RegsS s p L q cap)
    (h : exec env sl f Lib.hex0BodyS s = some (s', oc)) : RegsS s' p L q cap :=
  hr.of_agree (fun r hrmem => exec_frame_rget env sl f _ s s' oc h r (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrmem
    rcases hrmem with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide))

/-! ### The read-char prefix of `hex0BodyS`: `add 40 10 5; lbu 7 40 0; addi 41 5 1`.
    Loads the char at `p+idx` into reg 7 and computes `idx+1` into reg 41. -/

/-- The post-prefix state: reg 40 = p+idx, reg 7 = char, reg 41 = idx+1. -/
def prefSt (s0 : St) (p idx : Word) : St :=
  ((s0.rset 40 (p+idx)).rset 7 ((s0.mem (p+idx)).setWidth 64)).rset 41 (idx+1)

theorem hexPrefix_exec (f : Nat) (s0 : St) (p idx : Word) (rest : Stmt)
    (h10 : s0.rget 10 = p) (h5 : s0.rget 5 = idx) :
    exec env sl (f+4) (.seq (.add 40 10 5) (.seq (.lbu 7 40 0) (.seq (.addi 41 5 1) rest))) s0
      = exec env sl (f+1) rest (prefSt s0 p idx) := by
  have ha : exec env sl (f+3) (.add 40 10 5) s0 = some (s0.rset 40 (p+idx), .normal) := by
    rw [show f+3=(f+2)+1 from rfl, exec_add, h10, h5]
  have hl : exec env sl (f+2) (.lbu 7 40 0) (s0.rset 40 (p+idx))
      = some ((s0.rset 40 (p+idx)).rset 7 ((s0.mem (p+idx)).setWidth 64), .normal) := by
    rw [show f+2=(f+1)+1 from rfl, exec_lbu]
    simp only [rget_rset_eq _ 40 _ (by decide), zero_signExtend, wadd_zero, loadByte_eq, rset_mem]
  have haa : exec env sl (f+1) (.addi 41 5 1)
        ((s0.rset 40 (p+idx)).rset 7 ((s0.mem (p+idx)).setWidth 64))
      = some (prefSt s0 p idx, .normal) := by
    rw [exec_addi, one_signExtend, prefSt]
    simp only [rget_rset_ne _ 7 5 _ (by decide), rget_rset_ne _ 40 5 _ (by decide), h5]
  rw [show f+4=(f+3)+1 from rfl, exec_seq_normal (h := ha),
      show f+3=(f+2)+1 from rfl, exec_seq_normal (h := hl),
      show f+2=(f+1)+1 from rfl, exec_seq_normal (h := haa)]

end LowIR.SSA
