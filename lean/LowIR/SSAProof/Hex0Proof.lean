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
  geuL_true geuL_false slt_true slt_false tn regionBytes boundedRun commentSkip
  lowStop lowStop_iff regionBytes_snoc regionBytes_store_self ofNat_succ
  boundedRun_cons boundedRun_nil_coreSpec commentSkip_le commentSkip_get
  commentSkip_run_ne decodeS_comment_reconcile
  decodeS_high_space decodeS_high_comment decodeS_high_badhi decodeS_high_goodhi
  decodeS_high_nil decodeS_low_nil decodeS_low_split decodeS_low_badlo decodeS_low_goodlo
  Disjoint)

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

/-! ### Phase 3 — `skipCommentS`, the inner comment-scan `while`.

    An always-true inner loop; both exits `cont 1` (to the OUTER hex0 loop),
    which the inner `while` shifts to `cont 0` and delivers. No guard register,
    no `gOf` model, no poison flag — contrast Ctrl's `cgGuard`/`skip_body`/
    `skip_loop`/`skipComment_eff` chain (~170 lines). -/

/-- The inner scan body (matches `Lib.skipCommentS`'s body). -/
def scBody (j j1 a b : Reg) : Stmt :=
  .ife .lt j 11 []
    (.seq (.add a 10 j) <| .seq (.lbu b a 0)
      (.ife .eq b 24 []
        (.cont 1 [.reg j, .reg 6])
        (.seq (.addi j1 j 1) (.cont 0 [.reg j1]))))
    (.cont 1 [.reg j, .reg 6])

/-- The inner scan `while` with explicit `inits` (the back-edge rebinds them). -/
def scWhile (j j1 a b : Reg) (inits : List Opnd) : Stmt :=
  .«while» [] inits [j] .geu 0 0 (scBody j j1 a b) (.cont 1 [.reg j, .reg 6])

theorem skipCommentS_eq (i1 j j1 a b : Reg) :
    Lib.skipCommentS i1 j j1 a b = scWhile j j1 a b [.reg i1] := rfl

/-- Register-distinctness bundle for the four scratch names (discharged by
    `decide` at each concrete call site). -/
def SCok (j j1 a b : Reg) : Prop :=
  j ≠ 0 ∧ j1 ≠ 0 ∧ a ≠ 0 ∧ b ≠ 0 ∧
  (6:Reg) ≠ j ∧ (10:Reg) ≠ j ∧ (11:Reg) ≠ j ∧ (24:Reg) ≠ j ∧
  (24:Reg) ≠ a ∧ (24:Reg) ≠ b ∧ j ≠ a ∧ j ≠ b ∧ (6:Reg) ≠ a ∧ (6:Reg) ≠ b ∧
  (10:Reg) ≠ j1 ∧ (10:Reg) ≠ a ∧ (10:Reg) ≠ b ∧
  (11:Reg) ≠ j1 ∧ (11:Reg) ≠ a ∧ (11:Reg) ≠ b ∧
  (24:Reg) ≠ j1 ∧ (6:Reg) ≠ j1

/-- The comment-scan loop: from `cur`, advance `d` non-`\n` chars to the first
    `\n`/EOF, delivered as `cont 0 [cur + d, olen]` to the outer loop. Induction
    on the skip distance `d` (the `commentSkip` length, connected in `main_loop`).
    `s.mem` unchanged.

    Fuels are written as `f + k` (never bare numerals) so the `f+k = (f+(k-1))+1`
    rewrites cannot accidentally hit the register literals (6, 10, 11, 24, …). -/
theorem skip_loopS (p L olen : Word) (j j1 a b : Reg) (hok : SCok j j1 a b)
    (hL : L.toNat < 2^63) :
    ∀ (d : Nat) (s : St) (cur : Word) (inits : List Opnd),
      inits.map (evalOpnd s) = [cur] →
      s.rget 10 = p → s.rget 11 = L → s.rget 24 = 10 → s.rget 6 = olen →
      cur.toNat + d < 2^63 →
      (∀ k, k < d → (cur + BitVec.ofNat 64 k).toNat < L.toNat
              ∧ (s.mem (p + (cur + BitVec.ofNat 64 k))).toNat ≠ 10) →
      (L.toNat ≤ (cur + BitVec.ofNat 64 d).toNat
              ∨ (s.mem (p + (cur + BitVec.ofNat 64 d))).toNat = 10) →
      ∃ F s', exec env sl F (scWhile j j1 a b inits) s
          = some (s', .cont 0 [cur + BitVec.ofNat 64 d, olen])
        ∧ s'.mem = s.mem := by
  obtain ⟨hj0,hj10,ha0,hb0,h6j,h10j,h11j,h24j,h24a,h24b,hja,hjb,h6a,h6b,
          h10j1,h10a,h10b,h11j1,h11a,h11b,h24j1,h6j1⟩ := hok
  intro d
  induction d with
  | zero =>
    intro s cur inits hev h10 h11 h24 h6 hbd _ hexit
    rw [cur_zero] at hexit
    have hcb : cur.toNat < 2^63 := by omega
    obtain ⟨s0, hs0⟩ : ∃ y, y = bindOuts s [j] (inits.map (evalOpnd s)) := ⟨_, rfl⟩
    have hbo : s0 = s.rset j cur := by rw [hs0, hev]; rfl
    have hg_j : s0.rget j = cur := by rw [hbo]; exact rget_rset_eq _ _ _ hj0
    have hg_10 : s0.rget 10 = p := by rw [hbo, rget_rset_ne _ _ _ _ h10j]; exact h10
    have hg_11 : s0.rget 11 = L := by rw [hbo, rget_rset_ne _ _ _ _ h11j]; exact h11
    have hg_24 : s0.rget 24 = 10 := by rw [hbo, rget_rset_ne _ _ _ _ h24j]; exact h24
    have hg_6 : s0.rget 6 = olen := by rw [hbo, rget_rset_ne _ _ _ _ h6j]; exact h6
    have hg_mem : s0.mem = s.mem := by rw [hbo]; simp
    have hguard : evalCond .geu (s0.rget 0) (s0.rget 0) = true := by rw [rget_zero]; decide
    have hlen1 : inits.length = [j].length := by have := congrArg List.length hev; simpa using this
    -- prefix (add/lbu), valid regardless of the exit branch
    have hadd : ∀ f, exec env sl (f+4) (.add a 10 j) s0 = some (s0.rset a (p+cur), .normal) := by
      intro f; rw [show f+4 = (f+3)+1 from rfl, exec_add, hg_10, hg_j]
    have e_b : ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64)).rget b
        = (s.mem (p+cur)).setWidth 64 := rget_rset_eq _ _ _ hb0
    have e_24 : ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64)).rget 24 = 10 := by
      rw [rget_rset_ne _ _ _ _ h24b, rget_rset_ne _ _ _ _ h24a]; exact hg_24
    have e_j : ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64)).rget j = cur := by
      rw [rget_rset_ne _ b j _ hjb, rget_rset_ne _ a j _ hja]; exact hg_j
    have e_6 : ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64)).rget 6 = olen := by
      rw [rget_rset_ne _ _ _ _ h6b, rget_rset_ne _ _ _ _ h6a]; exact hg_6
    have hlbu : ∀ f, exec env sl (f+3) (.lbu b a 0) (s0.rset a (p+cur))
        = some ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64), .normal) := by
      intro f; rw [show f+3 = (f+2)+1 from rfl, exec_lbu]
      simp only [rget_rset_eq _ a _ ha0, zero_signExtend, wadd_zero, loadByte_eq, rset_mem, hg_mem]
    by_cases hlt : cur.toNat < L.toNat
    · -- newline exit: cur < L, so from hexit the byte is '\n'
      have hmemnl : (s.mem (p+cur)).toNat = 10 := by
        rcases hexit with h | h
        · omega
        · exact h
      have hcl : evalCond .lt (s0.rget j) (s0.rget 11) = true := by
        rw [hg_j, hg_11]; exact slt_true hcb hL hlt
      have hife2 : ∀ f, exec env sl (f+3) (.ife .eq b 24 [] (.cont 1 [.reg j, .reg 6])
            (.seq (.addi j1 j 1) (.cont 0 [.reg j1])))
            ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64))
          = some ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64), .cont 1 [cur, olen]) := by
        intro f
        rw [show f+3 = (f+2)+1 from rfl, exec_ife_then (hc := ceqS_true 10 e_b e_24 (by decide) hmemnl),
            show f+2 = (f+1)+1 from rfl, exec_cont, catch0_cont]
        simp only [List.map_cons, evalOpnd_reg, List.map_nil, e_j, e_6]
      have hbody : ∀ f, exec env sl (f+6) (scBody j j1 a b) s0
          = some ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64), .cont 1 [cur, olen]) := by
        intro f
        show exec env sl (f+6) (scBody j j1 a b) s0 = _
        unfold scBody
        rw [show f+6 = (f+5)+1 from rfl, exec_ife_then (hc := hcl),
            show f+5 = (f+4)+1 from rfl, exec_seq_normal (h := hadd f),
            show f+4 = (f+3)+1 from rfl, exec_seq_normal (h := hlbu f),
            hife2 f, catch0_cont]
      refine ⟨0+6+1, (s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64), ?_, by simp [hg_mem]⟩
      unfold scWhile
      rw [exec_while_contS (hlen := hlen1) (hs0 := hs0) (hc := hguard) (k := 0) (hb := hbody 0),
          cur_zero]
    · -- EOF exit: cur ≥ L, ELSE branch
      have hcl : evalCond .lt (s0.rget j) (s0.rget 11) = false := by
        rw [hg_j, hg_11]; exact slt_false hcb hL (by omega)
      have hbody : ∀ f, exec env sl (f+6) (scBody j j1 a b) s0
          = some (s0, .cont 1 [cur, olen]) := by
        intro f
        show exec env sl (f+6) (scBody j j1 a b) s0 = _
        unfold scBody
        rw [show f+6 = (f+5)+1 from rfl, exec_ife_else (hc := hcl),
            show f+5 = (f+4)+1 from rfl, exec_cont, catch0_cont]
        simp only [List.map_cons, evalOpnd_reg, List.map_nil, hg_j, hg_6]
      refine ⟨0+6+1, s0, ?_, by rw [hg_mem]⟩
      unfold scWhile
      rw [exec_while_contS (hlen := hlen1) (hs0 := hs0) (hc := hguard) (k := 0) (hb := hbody 0),
          cur_zero]
  | succ d0 ih =>
    intro s cur inits hev h10 h11 h24 h6 hbd hdig hexit
    have hcb : cur.toNat < 2^63 := by omega
    have hc1 : (cur+1).toNat = cur.toNat + 1 := by bv_omega
    obtain ⟨s0, hs0⟩ : ∃ y, y = bindOuts s [j] (inits.map (evalOpnd s)) := ⟨_, rfl⟩
    have hbo : s0 = s.rset j cur := by rw [hs0, hev]; rfl
    have hg_j : s0.rget j = cur := by rw [hbo]; exact rget_rset_eq _ _ _ hj0
    have hg_10 : s0.rget 10 = p := by rw [hbo, rget_rset_ne _ _ _ _ h10j]; exact h10
    have hg_11 : s0.rget 11 = L := by rw [hbo, rget_rset_ne _ _ _ _ h11j]; exact h11
    have hg_24 : s0.rget 24 = 10 := by rw [hbo, rget_rset_ne _ _ _ _ h24j]; exact h24
    have hg_6 : s0.rget 6 = olen := by rw [hbo, rget_rset_ne _ _ _ _ h6j]; exact h6
    have hg_mem : s0.mem = s.mem := by rw [hbo]; simp
    have hguard : evalCond .geu (s0.rget 0) (s0.rget 0) = true := by rw [rget_zero]; decide
    have hlen1 : inits.length = [j].length := by have := congrArg List.length hev; simpa using this
    have hd0 := hdig 0 (by omega); rw [cur_zero] at hd0
    obtain ⟨hlt0, hne0⟩ := hd0
    have hcl : evalCond .lt (s0.rget j) (s0.rget 11) = true := by
      rw [hg_j, hg_11]; exact slt_true hcb hL hlt0
    have hadd : ∀ f, exec env sl (f+4) (.add a 10 j) s0 = some (s0.rset a (p+cur), .normal) := by
      intro f; rw [show f+4 = (f+3)+1 from rfl, exec_add, hg_10, hg_j]
    have e_b : ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64)).rget b
        = (s.mem (p+cur)).setWidth 64 := rget_rset_eq _ _ _ hb0
    have e_24 : ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64)).rget 24 = 10 := by
      rw [rget_rset_ne _ _ _ _ h24b, rget_rset_ne _ _ _ _ h24a]; exact hg_24
    have e_j : ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64)).rget j = cur := by
      rw [rget_rset_ne _ b j _ hjb, rget_rset_ne _ a j _ hja]; exact hg_j
    have hlbu : ∀ f, exec env sl (f+3) (.lbu b a 0) (s0.rset a (p+cur))
        = some ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64), .normal) := by
      intro f; rw [show f+3 = (f+2)+1 from rfl, exec_lbu]
      simp only [rget_rset_eq _ a _ ha0, zero_signExtend, wadd_zero, loadByte_eq, rset_mem, hg_mem]
    obtain ⟨s1c, hs1c⟩ : ∃ y, y = ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64)).rset j1 (cur+1) :=
      ⟨_, rfl⟩
    have hife2 : ∀ f, exec env sl (f+3) (.ife .eq b 24 [] (.cont 1 [.reg j, .reg 6])
          (.seq (.addi j1 j 1) (.cont 0 [.reg j1])))
          ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64))
        = some (s1c, .cont 0 [cur+1]) := by
      intro f
      have haddi : ∀ g, exec env sl (g+1) (.addi j1 j 1)
            ((s0.rset a (p+cur)).rset b ((s.mem (p+cur)).setWidth 64)) = some (s1c, .normal) := by
        intro g; rw [exec_addi, e_j, one_signExtend, hs1c]
      have hcont : ∀ g, exec env sl (g+1) (.cont 0 [.reg j1]) s1c = some (s1c, .cont 0 [cur+1]) := by
        intro g; rw [exec_cont]
        simp only [List.map_cons, evalOpnd_reg, List.map_nil, hs1c, rget_rset_eq _ j1 _ hj10]
      rw [show f+3 = (f+2)+1 from rfl, exec_ife_else (hc := ceqS_false 10 e_b e_24 (by decide) hne0),
          show f+2 = (f+1)+1 from rfl, exec_seq_normal (h := haddi f), hcont f, catch0_cont]
    have hbody : ∀ f, exec env sl (f+6) (scBody j j1 a b) s0 = some (s1c, .cont 0 [cur+1]) := by
      intro f
      show exec env sl (f+6) (scBody j j1 a b) s0 = _
      unfold scBody
      rw [show f+6 = (f+5)+1 from rfl, exec_ife_then (hc := hcl),
          show f+5 = (f+4)+1 from rfl, exec_seq_normal (h := hadd f),
          show f+4 = (f+3)+1 from rfl, exec_seq_normal (h := hlbu f),
          hife2 f, catch0_cont]
    have hs1c_10 : s1c.rget 10 = p := by
      rw [hs1c, rget_rset_ne _ _ _ _ h10j1, rget_rset_ne _ _ _ _ h10b, rget_rset_ne _ _ _ _ h10a]; exact hg_10
    have hs1c_11 : s1c.rget 11 = L := by
      rw [hs1c, rget_rset_ne _ _ _ _ h11j1, rget_rset_ne _ _ _ _ h11b, rget_rset_ne _ _ _ _ h11a]; exact hg_11
    have hs1c_24 : s1c.rget 24 = 10 := by
      rw [hs1c, rget_rset_ne _ _ _ _ h24j1, rget_rset_ne _ _ _ _ h24b, rget_rset_ne _ _ _ _ h24a]; exact hg_24
    have hs1c_6 : s1c.rget 6 = olen := by
      rw [hs1c, rget_rset_ne _ _ _ _ h6j1, rget_rset_ne _ _ _ _ h6b, rget_rset_ne _ _ _ _ h6a]; exact hg_6
    have hs1c_mem : s1c.mem = s.mem := by rw [hs1c]; simp [hg_mem]
    have hev' : ([Opnd.const (cur+1)].map (evalOpnd s1c)) = [cur+1] := by simp
    have hbd' : (cur+1).toNat + d0 < 2^63 := by rw [hc1]; omega
    have hdig' : ∀ k, k < d0 → ((cur+1) + BitVec.ofNat 64 k).toNat < L.toNat
        ∧ (s1c.mem (p + ((cur+1) + BitVec.ofNat 64 k))).toNat ≠ 10 := by
      intro k hk; rw [hs1c_mem, ← cur_step]; exact hdig (k+1) (by omega)
    have hexit' : L.toNat ≤ ((cur+1) + BitVec.ofNat 64 d0).toNat
        ∨ (s1c.mem (p + ((cur+1) + BitVec.ofNat 64 d0))).toNat = 10 := by
      rw [hs1c_mem, ← cur_step]; exact hexit
    obtain ⟨F, s', hF, hmem'⟩ :=
      ih s1c (cur+1) [.const (cur+1)] hev' hs1c_10 hs1c_11 hs1c_24 hs1c_6 hbd' hdig' hexit'
    refine ⟨max 6 F + 1, s', ?_, by rw [hmem', hs1c_mem]⟩
    unfold scWhile
    rw [exec_while_cont0 (hlen := hlen1) (hs0 := hs0) (hc := hguard)
          (hb := exec_mono_le env sl (Nat.le_max_left 6 F) (hbody 0)) (hvs := rfl)]
    rw [show ([cur+1].map Opnd.const) = [Opnd.const (cur+1)] from rfl, cur_step]
    exact exec_mono_le env sl (Nat.le_max_right 6 F) hF

/-! ### Phase 4 — the loop body. Straight-line composition helpers (existential
    fuel, `exec_mono_le` to align), then `body_space`/`body_comment`/`hexPathS_eff`
    /`body_hex`, the three char-class outcomes of `hex0BodyS`. -/

/-- Existential-fuel `seq` composition: a normal step then anything. -/
theorem exec_seqE {s s' s'' : St} {a b : Stmt} {oc : Outcome}
    (ha : ∃ fa, exec env sl fa a s = some (s', .normal))
    (hb : ∃ fb, exec env sl fb b s' = some (s'', oc)) :
    ∃ f, exec env sl f (.seq a b) s = some (s'', oc) := by
  obtain ⟨fa, ha⟩ := ha; obtain ⟨fb, hb⟩ := hb
  refine ⟨max fa fb + 1, ?_⟩
  rw [exec_seq_normal (h := exec_mono_le env sl (Nat.le_max_left fa fb) ha)]
  exact exec_mono_le env sl (Nat.le_max_right fa fb) hb

/-- `err code` returns `[code, olen]` (status + current output length). -/
theorem exec_errS (f code : Nat) (s : St) :
    exec env sl (f+1) (Lib.err code) s = some (s, .ret [BitVec.ofNat 64 code, s.rget 6]) := by
  unfold Lib.err; rw [exec_ret]; simp

/-- `ife c a b [] (err code) .skip`, guard true → return `[code, olen]`. -/
theorem ifeErrS_true (code : Nat) (c : Cond) (a b : Reg) (s : St)
    (hc : evalCond c (s.rget a) (s.rget b) = true) :
    ∃ f, exec env sl f (.ife c a b [] (Lib.err code) .skip) s
      = some (s, .ret [BitVec.ofNat 64 code, s.rget 6]) := by
  refine ⟨0+1+1, ?_⟩
  rw [exec_ife_then (hc := hc), exec_errS, catch0_ret]

/-- `ife c a b [] (err code) .skip`, guard false → fall through unchanged. -/
theorem ifeErrS_false (code : Nat) (c : Cond) (a b : Reg) (s : St)
    (hc : evalCond c (s.rget a) (s.rget b) = false) :
    ∃ f, exec env sl f (.ife c a b [] (Lib.err code) .skip) s = some (s, .normal) := by
  refine ⟨0+1+1, ?_⟩
  rw [exec_ife_else (hc := hc), exec_skip, catch0_nil_normal]

/-- Existential-fuel `seq` where the first statement returns from the function. -/
theorem exec_seqE_ret {s s' : St} {a b : Stmt} {vs : List Word}
    (ha : ∃ fa, exec env sl fa a s = some (s', .ret vs)) :
    ∃ f, exec env sl f (.seq a b) s = some (s', .ret vs) := by
  obtain ⟨fa, ha⟩ := ha; exact ⟨fa+1, exec_seq_ret (b := b) (h := ha)⟩

/-- Memory congruence for `storeByte` under equal underlying memories. -/
theorem storeByte_mem_congr {s0 s1 : St} (a : Word) (b : Byte) (h : s0.mem = s1.mem) :
    (s0.storeByte a b).mem = (s1.storeByte a b).mem := by
  show (fun x => if x = a then b else s0.mem x) = (fun x => if x = a then b else s1.mem x)
  rw [h]

/-- `storeByte` leaves the register file untouched. -/
@[simp] theorem rget_storeByte (s : St) (a : Word) (b : Byte) (r : Reg) :
    (s.storeByte a b).rget r = s.rget r := rfl

/-! ### `hexPathS_eff` — the `<BYTE>` two-nibble path, six mutually-exclusive
    outcomes. `err code = .ret [code, olen]`; the success arm `cont 0 [idx+2,
    olen+1]` with the emitted byte stored at `q+olen`. The status register and
    `Regs` re-establishment of the Ctrl version are gone. -/
theorem hexPathS_eff (s : St) (p L q cap olen : Word) (idx : Nat) (chi : Byte)
    (hr : RegsS s p L q cap) (h6 : s.rget 6 = olen)
    (h41 : s.rget 41 = BitVec.ofNat 64 (idx+1)) (h7 : s.rget 7 = chi.setWidth 64)
    (hidx1 : idx + 1 < 2^64) :
    (pnibR chi = 255 ∧ ∃ f st', exec env sl f Lib.hexPathS s
        = some (st', .ret [BitVec.ofNat 64 5, olen]) ∧ st'.mem = s.mem)
  ∨ (pnibR chi ≠ 255 ∧ L.toNat ≤ idx+1 ∧ ∃ f st', exec env sl f Lib.hexPathS s
        = some (st', .ret [BitVec.ofNat 64 4, olen]) ∧ st'.mem = s.mem)
  ∨ (pnibR chi ≠ 255 ∧ idx+1 < L.toNat ∧ lowStop (s.mem (p + BitVec.ofNat 64 (idx+1)))
        ∧ ∃ f st', exec env sl f Lib.hexPathS s = some (st', .ret [BitVec.ofNat 64 3, olen])
        ∧ st'.mem = s.mem)
  ∨ (pnibR chi ≠ 255 ∧ idx+1 < L.toNat ∧ ¬ lowStop (s.mem (p + BitVec.ofNat 64 (idx+1)))
        ∧ pnibR (s.mem (p + BitVec.ofNat 64 (idx+1))) = 255
        ∧ ∃ f st', exec env sl f Lib.hexPathS s = some (st', .ret [BitVec.ofNat 64 5, olen])
        ∧ st'.mem = s.mem)
  ∨ (pnibR chi ≠ 255 ∧ idx+1 < L.toNat ∧ ¬ lowStop (s.mem (p + BitVec.ofNat 64 (idx+1)))
        ∧ pnibR (s.mem (p + BitVec.ofNat 64 (idx+1))) ≠ 255 ∧ cap.toNat ≤ olen.toNat
        ∧ ∃ f st', exec env sl f Lib.hexPathS s = some (st', .ret [BitVec.ofNat 64 2, olen])
        ∧ st'.mem = s.mem)
  ∨ (pnibR chi ≠ 255 ∧ idx+1 < L.toNat ∧ ¬ lowStop (s.mem (p + BitVec.ofNat 64 (idx+1)))
        ∧ pnibR (s.mem (p + BitVec.ofNat 64 (idx+1))) ≠ 255 ∧ olen.toNat < cap.toNat
        ∧ ∃ f st', exec env sl f Lib.hexPathS s
            = some (st', .cont 0 [BitVec.ofNat 64 (idx+1) + 1, olen + 1])
        ∧ st'.mem = (s.storeByte (q + olen)
              (((pnibR chi <<< 4) ||| pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))).setWidth 8)).mem) := by
  -- s1 = after `pnibS 28 54 55 7`
  obtain ⟨s1, hs1exec, hs1_28, hs1mem⟩ :=
    pnibS_eff env sl s 28 54 55 7 chi h7 hr.h17 hr.h20 hr.h21 hr.h22 hr.h23
      (by decide) (by decide) (by decide)
  have hs1 : ∀ (r : Reg), r ∉ SSA.defs (Lib.pnibS 28 54 55 7) → s1.rget r = s.rget r :=
    fun r h => exec_frame_rget env sl 6 _ s s1 .normal hs1exec r h
  have hs1_19 : s1.rget 19 = 255 := (hs1 19 (by decide)).trans hr.h19
  have hs1_6 : s1.rget 6 = olen := (hs1 6 (by decide)).trans h6
  have hstep1 : ∃ f, exec env sl f (Lib.pnibS 28 54 55 7) s = some (s1, .normal) := ⟨6, hs1exec⟩
  by_cases hbad : pnibR chi = 255
  · -- ARM A: bad high nibble → Unknown (5)
    refine Or.inl ⟨hbad, ?_⟩
    obtain ⟨f, hf⟩ := exec_seqE env sl hstep1
      (exec_seqE_ret env sl (ifeErrS_true env sl 5 .eq 28 19 s1 (weqS_true hs1_28 hs1_19 hbad)))
    exact ⟨f, s1, by rw [← hs1_6]; exact hf, hs1mem⟩
  · have hcond2 : evalCond .eq (s1.rget 28) (s1.rget 19) = false := weqS_false hs1_28 hs1_19 hbad
    have hstep2 : ∃ f, exec env sl f (.ife .eq 28 19 [] (Lib.err 5) .skip) s1 = some (s1, .normal) :=
      ifeErrS_false env sl 5 .eq 28 19 s1 hcond2
    have hs1_10 : s1.rget 10 = p := (hs1 10 (by decide)).trans hr.h10
    have hs1_41 : s1.rget 41 = BitVec.ofNat 64 (idx+1) := (hs1 41 (by decide)).trans h41
    have hs1_11 : s1.rget 11 = L := (hs1 11 (by decide)).trans hr.h11
    have hm1 : (BitVec.ofNat 64 (idx+1)).toNat = idx+1 := tn (idx+1) hidx1
    by_cases hodd : L.toNat ≤ idx+1
    · -- ARM B: input exhausted → OddEnd (4)
      refine Or.inr (Or.inl ⟨hbad, hodd, ?_⟩)
      have hcond3 : evalCond .geu (s1.rget 41) (s1.rget 11) = true :=
        geu_wwS_true hs1_41 hs1_11 (by rw [hm1]; exact hodd)
      obtain ⟨f, hf⟩ := exec_seqE env sl hstep1 (exec_seqE env sl hstep2
        (exec_seqE_ret env sl (ifeErrS_true env sl 4 .geu 41 11 s1 hcond3)))
      exact ⟨f, s1, by rw [← hs1_6]; exact hf, hs1mem⟩
    · have hlt1 : idx+1 < L.toNat := by omega
      have hcond3f : evalCond .geu (s1.rget 41) (s1.rget 11) = false :=
        geu_wwS_false hs1_41 hs1_11 (by rw [hm1]; exact hlt1)
      have hstep3 : ∃ f, exec env sl f (.ife .geu 41 11 [] (Lib.err 4) .skip) s1 = some (s1, .normal) :=
        ifeErrS_false env sl 4 .geu 41 11 s1 hcond3f
      -- read the low char: add 56 / lbu 57 / addi 58 → s6
      have hstep4 : ∃ f, exec env sl f (.add 56 10 41) s1
          = some (s1.rset 56 (p + BitVec.ofNat 64 (idx+1)), .normal) :=
        ⟨0+1, by rw [exec_add, hs1_10, hs1_41]⟩
      have hstep5 : ∃ f, exec env sl f (.lbu 57 56 0) (s1.rset 56 (p + BitVec.ofNat 64 (idx+1)))
          = some ((s1.rset 56 (p + BitVec.ofNat 64 (idx+1))).rset 57
              ((s.mem (p + BitVec.ofNat 64 (idx+1))).setWidth 64), .normal) := by
        refine ⟨0+1, ?_⟩; rw [exec_lbu]
        simp only [rget_rset_eq _ 56 _ (by decide), zero_signExtend, wadd_zero, loadByte_eq,
          rset_mem, hs1mem]
      obtain ⟨s6, hs6def⟩ : ∃ y, y = ((s1.rset 56 (p + BitVec.ofNat 64 (idx+1))).rset 57
          ((s.mem (p + BitVec.ofNat 64 (idx+1))).setWidth 64)).rset 58 (BitVec.ofNat 64 (idx+1) + 1) :=
        ⟨_, rfl⟩
      have hstep6 : ∃ f, exec env sl f (.addi 58 41 1)
            ((s1.rset 56 (p + BitVec.ofNat 64 (idx+1))).rset 57
              ((s.mem (p + BitVec.ofNat 64 (idx+1))).setWidth 64)) = some (s6, .normal) := by
        refine ⟨0+1, ?_⟩
        rw [exec_addi, one_signExtend, rget_rset_ne _ 57 41 _ (by decide),
            rget_rset_ne _ 56 41 _ (by decide), hs1_41, hs6def]
      -- s6 register facts
      have hs6 : ∀ (r : Reg), r ≠ 58 → r ≠ 57 → r ≠ 56 → s6.rget r = s1.rget r := by
        intro r h58 h57 h56
        rw [hs6def, rget_rset_ne _ _ _ _ h58, rget_rset_ne _ _ _ _ h57, rget_rset_ne _ _ _ _ h56]
      have hs1_24 : s1.rget 24 = 10 := (hs1 24 (by decide)).trans hr.h24
      have hs1_25 : s1.rget 25 = 32 := (hs1 25 (by decide)).trans hr.h25
      have hs1_26 : s1.rget 26 = 95 := (hs1 26 (by decide)).trans hr.h26
      have hs1_27 : s1.rget 27 = 35 := (hs1 27 (by decide)).trans hr.h27
      have hs1_18 : s1.rget 18 = 59 := (hs1 18 (by decide)).trans hr.h18
      have hs1_17 : s1.rget 17 = 55 := (hs1 17 (by decide)).trans hr.h17
      have hs1_20 : s1.rget 20 = 48 := (hs1 20 (by decide)).trans hr.h20
      have hs1_21 : s1.rget 21 = 57 := (hs1 21 (by decide)).trans hr.h21
      have hs1_22 : s1.rget 22 = 65 := (hs1 22 (by decide)).trans hr.h22
      have hs1_23 : s1.rget 23 = 70 := (hs1 23 (by decide)).trans hr.h23
      have hs1_12 : s1.rget 12 = q := (hs1 12 (by decide)).trans hr.h12
      have hs1_13 : s1.rget 13 = cap := (hs1 13 (by decide)).trans hr.h13
      have hs6_57 : s6.rget 57 = (s.mem (p + BitVec.ofNat 64 (idx+1))).setWidth 64 := by
        rw [hs6def, rget_rset_ne _ 58 57 _ (by decide), rget_rset_eq _ 57 _ (by decide)]
      have hs6_58 : s6.rget 58 = BitVec.ofNat 64 (idx+1) + 1 := by
        rw [hs6def, rget_rset_eq _ 58 _ (by decide)]
      have hs6_24 : s6.rget 24 = 10 := (hs6 24 (by decide) (by decide) (by decide)).trans hs1_24
      have hs6_25 : s6.rget 25 = 32 := (hs6 25 (by decide) (by decide) (by decide)).trans hs1_25
      have hs6_26 : s6.rget 26 = 95 := (hs6 26 (by decide) (by decide) (by decide)).trans hs1_26
      have hs6_27 : s6.rget 27 = 35 := (hs6 27 (by decide) (by decide) (by decide)).trans hs1_27
      have hs6_18 : s6.rget 18 = 59 := (hs6 18 (by decide) (by decide) (by decide)).trans hs1_18
      have hs6_17 : s6.rget 17 = 55 := (hs6 17 (by decide) (by decide) (by decide)).trans hs1_17
      have hs6_20 : s6.rget 20 = 48 := (hs6 20 (by decide) (by decide) (by decide)).trans hs1_20
      have hs6_21 : s6.rget 21 = 57 := (hs6 21 (by decide) (by decide) (by decide)).trans hs1_21
      have hs6_22 : s6.rget 22 = 65 := (hs6 22 (by decide) (by decide) (by decide)).trans hs1_22
      have hs6_23 : s6.rget 23 = 70 := (hs6 23 (by decide) (by decide) (by decide)).trans hs1_23
      have hs6_6  : s6.rget 6  = olen := (hs6 6 (by decide) (by decide) (by decide)).trans hs1_6
      have hs6_28 : s6.rget 28 = pnibR chi := (hs6 28 (by decide) (by decide) (by decide)).trans hs1_28
      have hs6_12 : s6.rget 12 = q := (hs6 12 (by decide) (by decide) (by decide)).trans hs1_12
      have hs6_13 : s6.rget 13 = cap := (hs6 13 (by decide) (by decide) (by decide)).trans hs1_13
      have hs6_19 : s6.rget 19 = 255 := (hs6 19 (by decide) (by decide) (by decide)).trans hs1_19
      have hmem6 : s6.mem = s.mem := by rw [hs6def]; simp [hs1mem]
      -- compose the first six statements onto any tail starting at `ife 57 …`
      have compose6 : ∀ {tail : Stmt} {s'' : St} {oc : Outcome},
          (∃ f, exec env sl f tail s6 = some (s'', oc)) →
          ∃ f, exec env sl f (.seq (Lib.pnibS 28 54 55 7) (.seq (.ife .eq 28 19 [] (Lib.err 5) .skip)
            (.seq (.ife .geu 41 11 [] (Lib.err 4) .skip) (.seq (.add 56 10 41) (.seq (.lbu 57 56 0)
            (.seq (.addi 58 41 1) tail)))))) s = some (s'', oc) := fun htail =>
        exec_seqE env sl hstep1 (exec_seqE env sl hstep2 (exec_seqE env sl hstep3
          (exec_seqE env sl hstep4 (exec_seqE env sl hstep5 (exec_seqE env sl hstep6 htail)))))
      by_cases hls : lowStop (s.mem (p + BitVec.ofNat 64 (idx+1)))
      · -- ARM C: low-stop char → Split (3)
        refine Or.inr (Or.inr (Or.inl ⟨hbad, hlt1, hls, ?_⟩))
        have hls' : (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat = 10
            ∨ (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat = 32
            ∨ (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat = 95
            ∨ (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat = 35
            ∨ (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat = 59 := hls
        rcases hls' with h | h | h | h | h
        · obtain ⟨f, hf⟩ := compose6 (exec_seqE_ret env sl
            (ifeErrS_true env sl 3 .eq 57 24 s6 (ceqS_true 10 hs6_57 hs6_24 (by decide) h)))
          exact ⟨f, s6, by rw [← hs6_6]; exact hf, hmem6⟩
        · obtain ⟨f, hf⟩ := compose6 (exec_seqE env sl
            (ifeErrS_false env sl 3 .eq 57 24 s6 (ceqS_false 10 hs6_57 hs6_24 (by decide) (by omega)))
            (exec_seqE_ret env sl
              (ifeErrS_true env sl 3 .eq 57 25 s6 (ceqS_true 32 hs6_57 hs6_25 (by decide) h))))
          exact ⟨f, s6, by rw [← hs6_6]; exact hf, hmem6⟩
        · obtain ⟨f, hf⟩ := compose6 (exec_seqE env sl
            (ifeErrS_false env sl 3 .eq 57 24 s6 (ceqS_false 10 hs6_57 hs6_24 (by decide) (by omega)))
            (exec_seqE env sl
              (ifeErrS_false env sl 3 .eq 57 25 s6 (ceqS_false 32 hs6_57 hs6_25 (by decide) (by omega)))
              (exec_seqE_ret env sl
                (ifeErrS_true env sl 3 .eq 57 26 s6 (ceqS_true 95 hs6_57 hs6_26 (by decide) h)))))
          exact ⟨f, s6, by rw [← hs6_6]; exact hf, hmem6⟩
        · obtain ⟨f, hf⟩ := compose6 (exec_seqE env sl
            (ifeErrS_false env sl 3 .eq 57 24 s6 (ceqS_false 10 hs6_57 hs6_24 (by decide) (by omega)))
            (exec_seqE env sl
              (ifeErrS_false env sl 3 .eq 57 25 s6 (ceqS_false 32 hs6_57 hs6_25 (by decide) (by omega)))
              (exec_seqE env sl
                (ifeErrS_false env sl 3 .eq 57 26 s6 (ceqS_false 95 hs6_57 hs6_26 (by decide) (by omega)))
                (exec_seqE_ret env sl
                  (ifeErrS_true env sl 3 .eq 57 27 s6 (ceqS_true 35 hs6_57 hs6_27 (by decide) h))))))
          exact ⟨f, s6, by rw [← hs6_6]; exact hf, hmem6⟩
        · obtain ⟨f, hf⟩ := compose6 (exec_seqE env sl
            (ifeErrS_false env sl 3 .eq 57 24 s6 (ceqS_false 10 hs6_57 hs6_24 (by decide) (by omega)))
            (exec_seqE env sl
              (ifeErrS_false env sl 3 .eq 57 25 s6 (ceqS_false 32 hs6_57 hs6_25 (by decide) (by omega)))
              (exec_seqE env sl
                (ifeErrS_false env sl 3 .eq 57 26 s6 (ceqS_false 95 hs6_57 hs6_26 (by decide) (by omega)))
                (exec_seqE env sl
                  (ifeErrS_false env sl 3 .eq 57 27 s6 (ceqS_false 35 hs6_57 hs6_27 (by decide) (by omega)))
                  (exec_seqE_ret env sl
                    (ifeErrS_true env sl 3 .eq 57 18 s6 (ceqS_true 59 hs6_57 hs6_18 (by decide) h)))))))
          exact ⟨f, s6, by rw [← hs6_6]; exact hf, hmem6⟩
      · -- not a low-stop char: read the second nibble
        have hn10 : (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat ≠ 10 := fun h => hls (Or.inl h)
        have hn32 : (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat ≠ 32 := fun h => hls (Or.inr (Or.inl h))
        have hn95 : (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat ≠ 95 := fun h => hls (Or.inr (Or.inr (Or.inl h)))
        have hn35 : (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat ≠ 35 := fun h => hls (Or.inr (Or.inr (Or.inr (Or.inl h))))
        have hn59 : (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat ≠ 59 := fun h => hls (Or.inr (Or.inr (Or.inr (Or.inr h))))
        obtain ⟨s7, hs7exec, hs7_29, hs7mem⟩ :=
          pnibS_eff env sl s6 29 59 60 57 (s.mem (p + BitVec.ofNat 64 (idx+1)))
            hs6_57 hs6_17 hs6_20 hs6_21 hs6_22 hs6_23 (by decide) (by decide) (by decide)
        have hs7 : ∀ (r : Reg), r ∉ SSA.defs (Lib.pnibS 29 59 60 57) → s7.rget r = s6.rget r :=
          fun r h => exec_frame_rget env sl 6 _ s6 s7 .normal hs7exec r h
        have hs7_19 : s7.rget 19 = 255 := (hs7 19 (by decide)).trans hs6_19
        have hs7_6  : s7.rget 6  = olen := (hs7 6 (by decide)).trans hs6_6
        have hs7_13 : s7.rget 13 = cap := (hs7 13 (by decide)).trans hs6_13
        have hs7_12 : s7.rget 12 = q := (hs7 12 (by decide)).trans hs6_12
        have hs7_28 : s7.rget 28 = pnibR chi := (hs7 28 (by decide)).trans hs6_28
        have hs7_58 : s7.rget 58 = BitVec.ofNat 64 (idx+1) + 1 := (hs7 58 (by decide)).trans hs6_58
        have hs7mem' : s7.mem = s.mem := hs7mem.trans hmem6
        -- 5 low-stop ifes (all false) + pnib29, then any tail on s7
        have hmid : ∀ {tail : Stmt} {s'' : St} {oc : Outcome},
            (∃ f, exec env sl f tail s7 = some (s'', oc)) →
            ∃ f, exec env sl f (.seq (.ife .eq 57 24 [] (Lib.err 3) .skip)
              (.seq (.ife .eq 57 25 [] (Lib.err 3) .skip) (.seq (.ife .eq 57 26 [] (Lib.err 3) .skip)
              (.seq (.ife .eq 57 27 [] (Lib.err 3) .skip) (.seq (.ife .eq 57 18 [] (Lib.err 3) .skip)
              (.seq (Lib.pnibS 29 59 60 57) tail)))))) s6 = some (s'', oc) := fun htail =>
          exec_seqE env sl (ifeErrS_false env sl 3 .eq 57 24 s6 (ceqS_false 10 hs6_57 hs6_24 (by decide) hn10))
            (exec_seqE env sl (ifeErrS_false env sl 3 .eq 57 25 s6 (ceqS_false 32 hs6_57 hs6_25 (by decide) hn32))
            (exec_seqE env sl (ifeErrS_false env sl 3 .eq 57 26 s6 (ceqS_false 95 hs6_57 hs6_26 (by decide) hn95))
            (exec_seqE env sl (ifeErrS_false env sl 3 .eq 57 27 s6 (ceqS_false 35 hs6_57 hs6_27 (by decide) hn35))
            (exec_seqE env sl (ifeErrS_false env sl 3 .eq 57 18 s6 (ceqS_false 59 hs6_57 hs6_18 (by decide) hn59))
            (exec_seqE env sl (show ∃ f, exec env sl f (Lib.pnibS 29 59 60 57) s6 = some (s7, .normal)
                from ⟨6, hs7exec⟩) htail)))))
        by_cases hbad2 : pnibR (s.mem (p + BitVec.ofNat 64 (idx+1))) = 255
        · -- ARM D: bad low nibble → Unknown (5)
          refine Or.inr (Or.inr (Or.inr (Or.inl ⟨hbad, hlt1, hls, hbad2, ?_⟩)))
          obtain ⟨f, hf⟩ := compose6 (hmid (exec_seqE_ret env sl
            (ifeErrS_true env sl 5 .eq 29 19 s7 (weqS_true hs7_29 hs7_19 hbad2))))
          exact ⟨f, s7, by rw [← hs7_6]; exact hf, hs7mem'⟩
        · by_cases hfull : cap.toNat ≤ olen.toNat
          · -- ARM E: output full → OutputShort (2)
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hbad, hlt1, hls, hbad2, hfull, ?_⟩))))
            obtain ⟨f, hf⟩ := compose6 (hmid (exec_seqE env sl
              (ifeErrS_false env sl 5 .eq 29 19 s7 (weqS_false hs7_29 hs7_19 hbad2))
              (exec_seqE_ret env sl
                (ifeErrS_true env sl 2 .geu 6 13 s7 (geu_wwS_true hs7_6 hs7_13 hfull)))))
            exact ⟨f, s7, by rw [← hs7_6]; exact hf, hs7mem'⟩
          · -- ARM F: write the byte, continue
            have hfull2 : olen.toNat < cap.toNat := by omega
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hbad, hlt1, hls, hbad2, hfull2, ?_⟩))))
            -- the write steps: slli / orr / add / sb / addi / cont
            have hslli : ∃ f, exec env sl f (.slli 50 28 4) s7
                = some (s7.rset 50 (pnibR chi <<< 4), .normal) :=
              ⟨0+1, by rw [exec_slli, hs7_28]⟩
            have horr : ∃ f, exec env sl f (.orr 51 50 29) (s7.rset 50 (pnibR chi <<< 4))
                = some ((s7.rset 50 (pnibR chi <<< 4)).rset 51
                    ((pnibR chi <<< 4) ||| pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))), .normal) := by
              refine ⟨0+1, ?_⟩
              rw [exec_orr, rget_rset_eq _ 50 _ (by decide), rget_rset_ne _ 50 29 _ (by decide), hs7_29]
            have hadd52 : ∃ f, exec env sl f (.add 52 12 6)
                  ((s7.rset 50 (pnibR chi <<< 4)).rset 51
                    ((pnibR chi <<< 4) ||| pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))))
                = some (((s7.rset 50 (pnibR chi <<< 4)).rset 51
                    ((pnibR chi <<< 4) ||| pnibR (s.mem (p + BitVec.ofNat 64 (idx+1))))).rset 52
                    (q + olen), .normal) := by
              refine ⟨0+1, ?_⟩
              rw [exec_add, rget_rset_ne _ 51 12 _ (by decide), rget_rset_ne _ 50 12 _ (by decide), hs7_12,
                  rget_rset_ne _ 51 6 _ (by decide), rget_rset_ne _ 50 6 _ (by decide), hs7_6]
            obtain ⟨s11, hs11def⟩ : ∃ y, y = (((s7.rset 50 (pnibR chi <<< 4)).rset 51
                ((pnibR chi <<< 4) ||| pnibR (s.mem (p + BitVec.ofNat 64 (idx+1))))).rset 52
                (q + olen)).storeByte (q + olen)
                (((pnibR chi <<< 4) ||| pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))).setWidth 8) := ⟨_, rfl⟩
            have hsb : ∃ f, exec env sl f (.sb 52 51 0)
                  (((s7.rset 50 (pnibR chi <<< 4)).rset 51
                    ((pnibR chi <<< 4) ||| pnibR (s.mem (p + BitVec.ofNat 64 (idx+1))))).rset 52 (q + olen))
                = some (s11, .normal) := by
              refine ⟨0+1, ?_⟩
              rw [exec_sb, rget_rset_eq _ 52 _ (by decide),
                  rget_rset_ne _ 52 51 _ (by decide), rget_rset_eq _ 51 _ (by decide),
                  zero_signExtend, wadd_zero, hs11def]
            have hs11_6 : s11.rget 6 = olen := by
              rw [hs11def, rget_storeByte, rget_rset_ne _ 52 6 _ (by decide),
                  rget_rset_ne _ 51 6 _ (by decide), rget_rset_ne _ 50 6 _ (by decide), hs7_6]
            have haddi53 : ∃ f, exec env sl f (.addi 53 6 1) s11 = some (s11.rset 53 (olen + 1), .normal) := by
              refine ⟨0+1, ?_⟩; rw [exec_addi, one_signExtend, hs11_6]
            have hs12_58 : (s11.rset 53 (olen + 1)).rget 58 = BitVec.ofNat 64 (idx+1) + 1 := by
              rw [rget_rset_ne _ 53 58 _ (by decide), hs11def, rget_storeByte,
                  rget_rset_ne _ 52 58 _ (by decide), rget_rset_ne _ 51 58 _ (by decide),
                  rget_rset_ne _ 50 58 _ (by decide), hs7_58]
            have hs12_53 : (s11.rset 53 (olen + 1)).rget 53 = olen + 1 := rget_rset_eq _ 53 _ (by decide)
            have hcont : ∃ f, exec env sl f (.cont 0 [.reg 58, .reg 53]) (s11.rset 53 (olen + 1))
                = some (s11.rset 53 (olen + 1), .cont 0 [BitVec.ofNat 64 (idx+1) + 1, olen + 1]) := by
              refine ⟨0+1, ?_⟩; rw [exec_cont]
              simp only [List.map_cons, evalOpnd_reg, List.map_nil, hs12_58, hs12_53]
            obtain ⟨f, hf⟩ := compose6 (hmid (exec_seqE env sl
              (ifeErrS_false env sl 5 .eq 29 19 s7 (weqS_false hs7_29 hs7_19 hbad2))
              (exec_seqE env sl
                (ifeErrS_false env sl 2 .geu 6 13 s7 (geu_wwS_false hs7_6 hs7_13 hfull2))
                (exec_seqE env sl hslli (exec_seqE env sl horr (exec_seqE env sl hadd52
                  (exec_seqE env sl hsb (exec_seqE env sl haddi53 hcont))))))))
            refine ⟨f, s11.rset 53 (olen + 1), hf, ?_⟩
            -- memory: the byte written at q+olen
            rw [rset_mem, hs11def]
            exact storeByte_mem_congr _ _ (by
              rw [rset_mem, rset_mem, rset_mem]; exact hs7mem')

/-! ### Dispatch on the read char: the loop body `hex0BodyS`. -/

/-- The char-dispatch chain of `hex0BodyS` (after the read prefix). -/
def hex0DispatchS : Stmt :=
  .ife .eq 7 27 [] (Lib.skipCommentS 41 42 43 44 45)
  (.ife .eq 7 18 [] (Lib.skipCommentS 41 46 47 48 49)
  (.ife .eq 7 24 [] (.cont 0 [.reg 41, .reg 6])
  (.ife .eq 7 25 [] (.cont 0 [.reg 41, .reg 6])
  (.ife .eq 7 26 [] (.cont 0 [.reg 41, .reg 6]) Lib.hexPathS))))

/-- Existential `ife _ _ _ [] t e`, guard true, arm outcome passes `catch0 []`. -/
theorem exec_ifeE_then_pass {s s'' : St} {c : Cond} {ca cb : Reg} {t e : Stmt} {oc : Outcome}
    (hc : evalCond c (s.rget ca) (s.rget cb) = true)
    (hpass : catch0 [] (some (s'', oc)) = some (s'', oc))
    (ht : ∃ f, exec env sl f t s = some (s'', oc)) :
    ∃ f, exec env sl f (.ife c ca cb [] t e) s = some (s'', oc) := by
  obtain ⟨f, ht⟩ := ht; exact ⟨f+1, by rw [exec_ife_then (hc := hc), ht, hpass]⟩

theorem exec_ifeE_else_pass {s s'' : St} {c : Cond} {ca cb : Reg} {t e : Stmt} {oc : Outcome}
    (hc : evalCond c (s.rget ca) (s.rget cb) = false)
    (hpass : catch0 [] (some (s'', oc)) = some (s'', oc))
    (he : ∃ f, exec env sl f e s = some (s'', oc)) :
    ∃ f, exec env sl f (.ife c ca cb [] t e) s = some (s'', oc) := by
  obtain ⟨f, he⟩ := he; exact ⟨f+1, by rw [exec_ife_else (hc := hc), he, hpass]⟩

/-! ### `prefSt` register/memory access. -/

theorem prefSt_rget_pres (s : St) (p idx : Word) (r : Reg)
    (h41 : r ≠ 41) (h7 : r ≠ 7) (h40 : r ≠ 40) : (prefSt s p idx).rget r = s.rget r := by
  unfold prefSt; rw [rget_rset_ne _ _ _ _ h41, rget_rset_ne _ _ _ _ h7, rget_rset_ne _ _ _ _ h40]

theorem prefSt_rget_7 (s : St) (p idx : Word) :
    (prefSt s p idx).rget 7 = (s.mem (p + idx)).setWidth 64 := by
  unfold prefSt; rw [rget_rset_ne _ 41 7 _ (by decide), rget_rset_eq _ 7 _ (by decide)]

theorem prefSt_rget_41 (s : St) (p idx : Word) : (prefSt s p idx).rget 41 = idx + 1 := by
  unfold prefSt; rw [rget_rset_eq _ 41 _ (by decide)]

theorem prefSt_mem (s : St) (p idx : Word) : (prefSt s p idx).mem = s.mem := by
  unfold prefSt; simp

theorem RegsS.pref {s : St} {p L q cap : Word} (hr : RegsS s p L q cap) (idx : Word) :
    RegsS (prefSt s p idx) p L q cap :=
  hr.of_agree (fun r hrmem => prefSt_rget_pres s p idx r
    (by rcases (by simpa using hrmem : _) with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by rcases (by simpa using hrmem : _) with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide)
    (by rcases (by simpa using hrmem : _) with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> decide))

/-- Lift a `hex0DispatchS` execution (from the post-prefix state) to `hex0BodyS`. -/
theorem body_lift (s : St) (p : Word) (idx : Word) (s'' : St) (oc : Outcome)
    (h10 : s.rget 10 = p) (h5 : s.rget 5 = idx)
    (hd : ∃ f, exec env sl f hex0DispatchS (prefSt s p idx) = some (s'', oc)) :
    ∃ f, exec env sl f Lib.hex0BodyS s = some (s'', oc) := by
  obtain ⟨fd, hd⟩ := hd
  refine ⟨fd + 4, ?_⟩
  rw [show Lib.hex0BodyS
        = .seq (.add 40 10 5) (.seq (.lbu 7 40 0) (.seq (.addi 41 5 1) hex0DispatchS)) from rfl,
      hexPrefix_exec env sl fd s p idx hex0DispatchS h10 h5]
  exact exec_mono_le env sl (Nat.le_succ fd) hd

/-- Space class (`\n`/` `/`_`): advance one char, continue. -/
theorem body_space (s : St) (p L q cap olen : Word) (idxNat : Nat) (chi : Byte)
    (hr : RegsS s p L q cap) (h5 : s.rget 5 = BitVec.ofNat 64 idxNat) (h6 : s.rget 6 = olen)
    (hchar : s.mem (p + BitVec.ofNat 64 idxNat) = chi)
    (hsp : chi.toNat = 10 ∨ chi.toNat = 32 ∨ chi.toNat = 95) :
    ∃ f st', exec env sl f Lib.hex0BodyS s
      = some (st', .cont 0 [BitVec.ofNat 64 idxNat + 1, olen]) ∧ st'.mem = s.mem := by
  obtain ⟨ps, hps⟩ : ∃ y, y = prefSt s p (BitVec.ofNat 64 idxNat) := ⟨_, rfl⟩
  have p7 : ps.rget 7 = chi.setWidth 64 := by rw [hps, prefSt_rget_7, hchar]
  have p41 : ps.rget 41 = BitVec.ofNat 64 idxNat + 1 := by rw [hps, prefSt_rget_41]
  have p6 : ps.rget 6 = olen := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide), h6]
  have p27 : ps.rget 27 = 35 := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h27
  have p18 : ps.rget 18 = 59 := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h18
  have p24 : ps.rget 24 = 10 := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h24
  have p25 : ps.rget 25 = 32 := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h25
  have p26 : ps.rget 26 = 95 := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h26
  have pmem : ps.mem = s.mem := by rw [hps, prefSt_mem]
  have hleaf : ∃ f, exec env sl f (.cont 0 [.reg 41, .reg 6]) ps
      = some (ps, .cont 0 [BitVec.ofNat 64 idxNat + 1, olen]) := by
    refine ⟨0+1, ?_⟩; rw [exec_cont]; simp only [List.map_cons, evalOpnd_reg, List.map_nil, p41, p6]
  have hpass : catch0 [] (some (ps, Outcome.cont 0 [BitVec.ofNat 64 idxNat + 1, olen]))
      = some (ps, .cont 0 [BitVec.ofNat 64 idxNat + 1, olen]) := catch0_cont _ _ _ _
  have hd : ∃ f, exec env sl f hex0DispatchS ps
      = some (ps, .cont 0 [BitVec.ofNat 64 idxNat + 1, olen]) := by
    rcases hsp with h | h | h
    · exact exec_ifeE_else_pass env sl (ceqS_false 35 p7 p27 (by decide) (by omega)) hpass
        (exec_ifeE_else_pass env sl (ceqS_false 59 p7 p18 (by decide) (by omega)) hpass
        (exec_ifeE_then_pass env sl (ceqS_true 10 p7 p24 (by decide) h) hpass hleaf))
    · exact exec_ifeE_else_pass env sl (ceqS_false 35 p7 p27 (by decide) (by omega)) hpass
        (exec_ifeE_else_pass env sl (ceqS_false 59 p7 p18 (by decide) (by omega)) hpass
        (exec_ifeE_else_pass env sl (ceqS_false 10 p7 p24 (by decide) (by omega)) hpass
        (exec_ifeE_then_pass env sl (ceqS_true 32 p7 p25 (by decide) h) hpass hleaf)))
    · exact exec_ifeE_else_pass env sl (ceqS_false 35 p7 p27 (by decide) (by omega)) hpass
        (exec_ifeE_else_pass env sl (ceqS_false 59 p7 p18 (by decide) (by omega)) hpass
        (exec_ifeE_else_pass env sl (ceqS_false 10 p7 p24 (by decide) (by omega)) hpass
        (exec_ifeE_else_pass env sl (ceqS_false 32 p7 p25 (by decide) (by omega)) hpass
        (exec_ifeE_then_pass env sl (ceqS_true 95 p7 p26 (by decide) h) hpass hleaf))))
  rw [hps] at hd
  obtain ⟨f, hf⟩ := body_lift env sl s p (BitVec.ofNat 64 idxNat) _ _ hr.h10 h5 hd
  exact ⟨f, _, hf, by rw [prefSt_mem]⟩

/-- Lift a `hexPathS` execution to `hex0BodyS` (all five dispatch tests fail). -/
theorem body_hex_lift (s : St) (p L q cap : Word) (idx : Word) (chi : Byte) (s'' : St) (oc : Outcome)
    (hr : RegsS s p L q cap) (h10 : s.rget 10 = p) (h5 : s.rget 5 = idx)
    (hchar : s.mem (p + idx) = chi)
    (hns : chi.toNat ≠ 10 ∧ chi.toNat ≠ 32 ∧ chi.toNat ≠ 95 ∧ chi.toNat ≠ 35 ∧ chi.toNat ≠ 59)
    (hpass : catch0 [] (some (s'', oc)) = some (s'', oc))
    (hx : ∃ f, exec env sl f Lib.hexPathS (prefSt s p idx) = some (s'', oc)) :
    ∃ f, exec env sl f Lib.hex0BodyS s = some (s'', oc) := by
  have p7 : (prefSt s p idx).rget 7 = chi.setWidth 64 := by rw [prefSt_rget_7, hchar]
  have p27 : (prefSt s p idx).rget 27 = 35 := by rw [prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h27
  have p18 : (prefSt s p idx).rget 18 = 59 := by rw [prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h18
  have p24 : (prefSt s p idx).rget 24 = 10 := by rw [prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h24
  have p25 : (prefSt s p idx).rget 25 = 32 := by rw [prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h25
  have p26 : (prefSt s p idx).rget 26 = 95 := by rw [prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h26
  exact body_lift env sl s p idx s'' oc h10 h5
    (exec_ifeE_else_pass env sl (ceqS_false 35 p7 p27 (by decide) hns.2.2.2.1) hpass
    (exec_ifeE_else_pass env sl (ceqS_false 59 p7 p18 (by decide) hns.2.2.2.2) hpass
    (exec_ifeE_else_pass env sl (ceqS_false 10 p7 p24 (by decide) hns.1) hpass
    (exec_ifeE_else_pass env sl (ceqS_false 32 p7 p25 (by decide) hns.2.1) hpass
    (exec_ifeE_else_pass env sl (ceqS_false 95 p7 p26 (by decide) hns.2.2.1) hpass hx)))))

/-- Comment class (`#`/`;`): skip to newline/EOF via the inner loop, continue. -/
theorem body_comment (s : St) (p L q cap olen : Word) (idxNat d : Nat) (chi : Byte)
    (hr : RegsS s p L q cap) (h5 : s.rget 5 = BitVec.ofNat 64 idxNat) (h6 : s.rget 6 = olen)
    (hchar : s.mem (p + BitVec.ofNat 64 idxNat) = chi) (hcm : chi.toNat = 35 ∨ chi.toNat = 59)
    (hL : L.toNat < 2^63) (hbd : (BitVec.ofNat 64 idxNat + 1).toNat + d < 2^63)
    (hdig : ∀ k, k < d → ((BitVec.ofNat 64 idxNat + 1) + BitVec.ofNat 64 k).toNat < L.toNat
        ∧ (s.mem (p + ((BitVec.ofNat 64 idxNat + 1) + BitVec.ofNat 64 k))).toNat ≠ 10)
    (hexit : L.toNat ≤ ((BitVec.ofNat 64 idxNat + 1) + BitVec.ofNat 64 d).toNat
        ∨ (s.mem (p + ((BitVec.ofNat 64 idxNat + 1) + BitVec.ofNat 64 d))).toNat = 10) :
    ∃ f st', exec env sl f Lib.hex0BodyS s
      = some (st', .cont 0 [(BitVec.ofNat 64 idxNat + 1) + BitVec.ofNat 64 d, olen]) ∧ st'.mem = s.mem := by
  obtain ⟨ps, hps⟩ : ∃ y, y = prefSt s p (BitVec.ofNat 64 idxNat) := ⟨_, rfl⟩
  have p7 : ps.rget 7 = chi.setWidth 64 := by rw [hps, prefSt_rget_7, hchar]
  have p41 : ps.rget 41 = BitVec.ofNat 64 idxNat + 1 := by rw [hps, prefSt_rget_41]
  have p10 : ps.rget 10 = p := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h10
  have p11 : ps.rget 11 = L := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h11
  have p24 : ps.rget 24 = 10 := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h24
  have p27 : ps.rget 27 = 35 := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h27
  have p18 : ps.rget 18 = 59 := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hr.h18
  have p6 : ps.rget 6 = olen := by rw [hps, prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide), h6]
  have pmem : ps.mem = s.mem := by rw [hps, prefSt_mem]
  have hev : ([Opnd.reg 41].map (evalOpnd ps)) = [BitVec.ofNat 64 idxNat + 1] := by
    simp only [List.map_cons, evalOpnd_reg, List.map_nil, p41]
  -- run the inner comment loop (j/j1/a/b picked per site)
  have run_scc : ∀ (j j1 a b : Reg), SCok j j1 a b →
      ∃ F s', exec env sl F (scWhile j j1 a b [.reg 41]) ps
        = some (s', .cont 0 [(BitVec.ofNat 64 idxNat + 1) + BitVec.ofNat 64 d, olen]) ∧ s'.mem = s.mem := by
    intro j j1 a b hok
    obtain ⟨F, s', hF, hmem⟩ := skip_loopS env sl p L olen j j1 a b hok hL d ps
      (BitVec.ofNat 64 idxNat + 1) [.reg 41] hev p10 p11 p24 p6 (by rw [pmem] at *; exact hbd)
      (fun k hk => by rw [pmem]; exact hdig k hk) (by rw [pmem]; exact hexit)
    exact ⟨F, s', hF, hmem.trans pmem⟩
  have hpass : ∀ (s' : St), catch0 [] (some (s', Outcome.cont 0
        [(BitVec.ofNat 64 idxNat + 1) + BitVec.ofNat 64 d, olen]))
      = some (s', .cont 0 [(BitVec.ofNat 64 idxNat + 1) + BitVec.ofNat 64 d, olen]) :=
    fun s' => catch0_cont _ _ _ _
  rcases hcm with h35 | h59
  · obtain ⟨F, s', hsc, hmem⟩ := run_scc 42 43 44 45 (by unfold SCok; decide)
    have hd : ∃ f, exec env sl f hex0DispatchS ps
        = some (s', .cont 0 [(BitVec.ofNat 64 idxNat + 1) + BitVec.ofNat 64 d, olen]) :=
      exec_ifeE_then_pass env sl (ceqS_true 35 p7 p27 (by decide) h35) (hpass s')
        ⟨_, by rw [skipCommentS_eq]; exact hsc⟩
    rw [hps] at hd
    obtain ⟨f, hf⟩ := body_lift env sl s p (BitVec.ofNat 64 idxNat) s' _ hr.h10 h5 hd
    exact ⟨f, s', hf, hmem⟩
  · obtain ⟨F, s', hsc, hmem⟩ := run_scc 46 47 48 49 (by unfold SCok; decide)
    have hd : ∃ f, exec env sl f hex0DispatchS ps
        = some (s', .cont 0 [(BitVec.ofNat 64 idxNat + 1) + BitVec.ofNat 64 d, olen]) :=
      exec_ifeE_else_pass env sl (ceqS_false 35 p7 p27 (by decide) (by omega)) (hpass s')
        (exec_ifeE_then_pass env sl (ceqS_true 59 p7 p18 (by decide) h59) (hpass s')
          ⟨_, by rw [skipCommentS_eq]; exact hsc⟩)
    rw [hps] at hd
    obtain ⟨f, hf⟩ := body_lift env sl s p (BitVec.ofNat 64 idxNat) s' _ hr.h10 h5 hd
    exact ⟨f, s', hf, hmem⟩

/-! ### Phase 5 — the main loop.

    Strong induction on `n = |inp| − idx` with the args-tuple invariant
    `inits.map (evalOpnd s) = [ofNat idx, ofNat olen]`; the frame theorem
    (`RegsS.frame`) carries the 15 const/param registers across each body. -/

/-- The `hex0S` main loop as a standalone args-tuple `while`. -/
def hex0WhileS (inits : List Opnd) : Stmt :=
  .«while» [] inits [5, 6] .lt 5 11 Lib.hex0BodyS (.ret [.const 0, .reg 6])

/-- `RegsS` survives binding the two loop args (regs 5, 6). -/
theorem RegsS.rset56 {s : St} {p L q cap : Word} (hr : RegsS s p L q cap) (a b : Word) :
    RegsS ((s.rset 5 a).rset 6 b) p L q cap := by
  refine hr.of_agree (fun r hrmem => ?_)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hrmem
  rcases hrmem with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;>
    rw [rget_rset_ne _ 6 _ _ (by decide), rget_rset_ne _ 5 _ _ (by decide)]

/-- Prog.St analogue of `regionBytes_store_self`: writing byte `n` leaves `[base, base+n)`. -/
theorem regionBytes_storeByte_self (s : St) (base : Word) (n : Nat) (b : Byte) (hn : n < 2^64) :
    regionBytes (s.storeByte (base + BitVec.ofNat 64 n) b).mem base n = regionBytes s.mem base n := by
  unfold regionBytes
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  show (if base + BitVec.ofNat 64 k = base + BitVec.ofNat 64 n then b else s.mem _).toNat = _
  rw [if_neg (by bv_omega)]

/-- **The hex0 main loop computes `boundedRun`.** -/
theorem main_loop (inp : List Nat) (p q : Word) (capN : Nat)
    (hinp : ∀ x ∈ inp, x < 256) (hlenb : inp.length < 2^63) (hcap : capN < 2^63)
    (hdisj : Disjoint ⟨p, inp.length⟩ ⟨q, capN⟩) :
    ∀ (n idx olen : Nat) (s : St) (produced : List Nat) (inits : List Opnd),
      n = inp.length - idx →
      inits.map (evalOpnd s) = [BitVec.ofNat 64 idx, BitVec.ofNat 64 olen] →
      RegsS s p (BitVec.ofNat 64 inp.length) q (BitVec.ofNat 64 capN) →
      idx ≤ inp.length → olen ≤ capN → olen = produced.length →
      (∀ k : Word, k.toNat < inp.length → s.mem (p + k) = BitVec.ofNat 8 (inp[k.toNat]!)) →
      regionBytes s.mem q olen = produced →
      ∃ F s' status outlen, exec env sl F (hex0WhileS inits) s
          = some (s', .ret [BitVec.ofNat 64 status, BitVec.ofNat 64 outlen])
        ∧ (status, regionBytes s'.mem q outlen, outlen)
            = boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
                (Hex0.decodeS .High (inp.drop idx)).2 capN := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro idx olen s produced inits hn hev hregs hidx holen holenp hbridge hout
  have hlen : inits.length = ([5, 6] : List Reg).length := by
    have := congrArg List.length hev; simpa using this
  obtain ⟨s0, hs0⟩ : ∃ y, y = bindOuts s [5, 6] (inits.map (evalOpnd s)) := ⟨_, rfl⟩
  have hbo : s0 = (s.rset 5 (BitVec.ofNat 64 idx)).rset 6 (BitVec.ofNat 64 olen) := by
    rw [hs0, hev]; rfl
  have hs0_5 : s0.rget 5 = BitVec.ofNat 64 idx := by rw [hbo]; simp
  have hs0_6 : s0.rget 6 = BitVec.ofNat 64 olen := by rw [hbo]; simp
  have hs0_10 : s0.rget 10 = p := by rw [hbo]; simp [hregs.h10]
  have hs0_11 : s0.rget 11 = BitVec.ofNat 64 inp.length := by rw [hbo]; simp [hregs.h11]
  have hs0mem : s0.mem = s.mem := by rw [hbo]; simp
  have hr_s0 : RegsS s0 p (BitVec.ofNat 64 inp.length) q (BitVec.ofNat 64 capN) := by
    rw [hbo]; exact hregs.rset56 _ _
  have hpc : produced.length ≤ capN := by omega
  by_cases hlt : idx < inp.length
  · -- inductive step: one body iteration
    have hkidx : (BitVec.ofNat 64 idx).toNat = idx := tn idx (by omega)
    have hvmem : inp[idx]! = inp[idx] := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    have hv : inp[idx]! < 256 := by rw [hvmem]; exact hinp _ (List.getElem_mem hlt)
    have hbr_idx : s.mem (p + BitVec.ofNat 64 idx) = BitVec.ofNat 8 (inp[idx]!) := by
      have hb := hbridge (BitVec.ofNat 64 idx) (by rw [hkidx]; exact hlt); rwa [hkidx] at hb
    have hcv : (s.mem (p + BitVec.ofNat 64 idx)).toNat = inp[idx]! := by
      rw [hbr_idx, BitVec.toNat_ofNat]; omega
    have hchar0 : s0.mem (p + BitVec.ofNat 64 idx) = s.mem (p + BitVec.ofNat 64 idx) := by rw [hs0mem]
    have hcond : evalCond .lt (s0.rget 5) (s0.rget 11) = true := by
      rw [hs0_5, hs0_11]
      exact slt_true (by rw [hkidx]; omega) (by rw [tn inp.length (by omega)]; omega)
        (by rw [hkidx, tn inp.length (by omega)]; exact hlt)
    have hdropc : inp.drop idx = inp[idx]! :: inp.drop (idx+1) := by
      rw [List.drop_eq_getElem_cons hlt, hvmem]
    rcases (show (inp[idx]! = 10 ∨ inp[idx]! = 32 ∨ inp[idx]! = 95)
        ∨ (inp[idx]! = 35 ∨ inp[idx]! = 59)
        ∨ (inp[idx]! ≠ 10 ∧ inp[idx]! ≠ 32 ∧ inp[idx]! ≠ 95 ∧ inp[idx]! ≠ 35 ∧ inp[idx]! ≠ 59)
        from by omega) with hsp | hcm | hns
    · -- SPACE: advance one, continue
      have hisS : Hex0.isSpace inp[idx]! = true := by
        unfold Hex0.isSpace Hex0.c_nl Hex0.c_sp Hex0.c_us; rcases hsp with h|h|h <;> simp [h]
      have hisC : Hex0.isComment inp[idx]! = false := by
        unfold Hex0.isComment Hex0.c_hash Hex0.c_semi; rcases hsp with h|h|h <;> simp [h]
      obtain ⟨fb, st1, heb, hbmem⟩ :=
        body_space env sl s0 p (BitVec.ofNat 64 inp.length) q (BitVec.ofNat 64 capN)
          (BitVec.ofNat 64 olen) idx (s.mem (p + BitVec.ofNat 64 idx)) hr_s0 hs0_5 hs0_6 hchar0
          (by rw [hcv]; exact hsp)
      have hr1 : RegsS st1 p (BitVec.ofNat 64 inp.length) q (BitVec.ofNat 64 capN) :=
        RegsS.frame env sl hr_s0 heb
      have hev' : ([Opnd.const (BitVec.ofNat 64 idx + 1), Opnd.const (BitVec.ofNat 64 olen)].map
            (evalOpnd st1)) = [BitVec.ofNat 64 (idx+1), BitVec.ofNat 64 olen] := by
        simp only [List.map_cons, evalOpnd_const, List.map_nil, ofNat_succ]
      have ebridge : ∀ k : Word, k.toNat < inp.length → st1.mem (p+k) = BitVec.ofNat 8 (inp[k.toNat]!) := by
        intro k hk; rw [hbmem, hs0mem]; exact hbridge k hk
      have eout : regionBytes st1.mem q olen = produced := by rw [hbmem, hs0mem]; exact hout
      obtain ⟨F, s', status, outlen, her, hbr'⟩ :=
        ih (inp.length - (idx+1)) (by omega) (idx+1) olen st1 produced
          [.const (BitVec.ofNat 64 idx + 1), .const (BitVec.ofNat 64 olen)] rfl hev' hr1
          (by omega) holen holenp ebridge eout
      have hstep : Hex0.decodeS .High (inp.drop idx) = Hex0.decodeS .High (inp.drop (idx+1)) := by
        rw [hdropc]; exact decodeS_high_space _ _ hisC hisS
      refine ⟨max fb F + 1, s', status, outlen, ?_, ?_⟩
      · show exec env sl (max fb F + 1) (hex0WhileS inits) s = _
        rw [hex0WhileS, exec_while_cont0 (hlen := hlen) (hs0 := hs0) (hc := hcond)
              (hb := exec_mono_le env sl (Nat.le_max_left fb F) heb) (hvs := rfl)]
        rw [show ([BitVec.ofNat 64 idx + 1, BitVec.ofNat 64 olen].map Opnd.const)
              = [Opnd.const (BitVec.ofNat 64 idx + 1), Opnd.const (BitVec.ofNat 64 olen)] from rfl]
        exact exec_mono_le env sl (Nat.le_max_right fb F) her
      · rw [hstep]; exact hbr'
    · -- COMMENT: skip to newline/EOF, continue
      have hisCt : Hex0.isComment inp[idx]! = true := by
        unfold Hex0.isComment Hex0.c_hash Hex0.c_semi; rcases hcm with h|h <;> simp [h]
      have hDle : commentSkip (inp.drop (idx+1)) ≤ inp.length - (idx+1) := by
        have := commentSkip_le (inp.drop (idx+1)); rwa [List.length_drop] at this
      have hdig : ∀ k, k < commentSkip (inp.drop (idx+1)) →
          ((BitVec.ofNat 64 idx + 1) + BitVec.ofNat 64 k).toNat < (BitVec.ofNat 64 inp.length).toNat
            ∧ (s.mem (p + ((BitVec.ofNat 64 idx + 1) + BitVec.ofNat 64 k))).toNat ≠ 10 := by
        intro j hj
        have hoff : (BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 j).toNat = idx+1+j := by
          rw [show BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 j = BitVec.ofNat 64 (idx+1+j) from by bv_omega]
          exact tn _ (by omega)
        have hlt2 : idx+1+j < inp.length := by omega
        refine ⟨by rw [hoff, tn inp.length (by omega)]; omega, ?_⟩
        have hmem := hbridge (BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 j) (by rw [hoff]; omega)
        rw [hoff] at hmem
        rw [hmem, BitVec.toNat_ofNat]
        have hidxval : inp[idx+1+j]! = inp[idx+1+j] := by
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2]
        have hlt256 : inp[idx+1+j]! < 256 := by rw [hidxval]; exact hinp _ (List.getElem_mem hlt2)
        have hne : inp[idx+1+j]! ≠ 10 := by
          have hr := commentSkip_run_ne (inp.drop (idx+1)) j hj
          rwa [show (inp.drop (idx+1))[j]! = inp[idx+1+j]! from by
            simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]] at hr
        omega
      have hz : (BitVec.ofNat 64 inp.length).toNat ≤ ((BitVec.ofNat 64 idx + 1)
            + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))).toNat
          ∨ (s.mem (p + ((BitVec.ofNat 64 idx + 1)
              + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))))).toNat = 10 := by
        by_cases hDlen : commentSkip (inp.drop (idx+1)) < (inp.drop (idx+1)).length
        · have hlt2 : idx+1+commentSkip (inp.drop (idx+1)) < inp.length := by
            rw [List.length_drop] at hDlen; omega
          have hoff : (BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))).toNat
              = idx+1+commentSkip (inp.drop (idx+1)) := by
            rw [show BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))
              = BitVec.ofNat 64 (idx+1+commentSkip (inp.drop (idx+1))) from by bv_omega]
            exact tn _ (by omega)
          refine Or.inr ?_
          have hmem := hbridge (BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1))))
            (by rw [hoff]; omega)
          rw [hoff] at hmem
          rw [hmem, BitVec.toNat_ofNat]
          have hg := commentSkip_get (inp.drop (idx+1)) hDlen
          rw [show (inp.drop (idx+1))[commentSkip (inp.drop (idx+1))]! = inp[idx+1+commentSkip (inp.drop (idx+1))]! from by
            simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop]] at hg
          rw [hg]
        · have hDeq : commentSkip (inp.drop (idx+1)) = inp.length - (idx+1) := by
            rw [List.length_drop] at hDlen; omega
          refine Or.inl ?_
          rw [show BitVec.ofNat 64 idx + 1 + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))
            = BitVec.ofNat 64 (idx+1+commentSkip (inp.drop (idx+1))) from by bv_omega]
          rw [tn inp.length (by omega), tn (idx+1+commentSkip (inp.drop (idx+1))) (by omega)]; omega
      obtain ⟨fb, st1, heb, hbmem⟩ :=
        body_comment env sl s0 p (BitVec.ofNat 64 inp.length) q (BitVec.ofNat 64 capN)
          (BitVec.ofNat 64 olen) idx (commentSkip (inp.drop (idx+1)))
          (s.mem (p + BitVec.ofNat 64 idx)) hr_s0 hs0_5 hs0_6 hchar0 (by rw [hcv]; exact hcm)
          (by rw [tn inp.length (by omega)]; omega)
          (by rw [show BitVec.ofNat 64 idx + 1 = BitVec.ofNat 64 (idx+1) from by bv_omega,
                tn (idx+1) (by omega)]; omega)
          (by intro k hk; rw [hs0mem]; exact hdig k hk) (by rw [hs0mem]; exact hz)
      have hr1 : RegsS st1 p (BitVec.ofNat 64 inp.length) q (BitVec.ofNat 64 capN) :=
        RegsS.frame env sl hr_s0 heb
      have hev' : ([Opnd.const ((BitVec.ofNat 64 idx + 1) + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))),
            Opnd.const (BitVec.ofNat 64 olen)].map (evalOpnd st1))
          = [BitVec.ofNat 64 (idx + 1 + commentSkip (inp.drop (idx+1))), BitVec.ofNat 64 olen] := by
        simp only [List.map_cons, evalOpnd_const, List.map_nil]
        rw [show (BitVec.ofNat 64 idx + 1) + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))
          = BitVec.ofNat 64 (idx + 1 + commentSkip (inp.drop (idx+1))) from by bv_omega]
      have ebridge : ∀ k : Word, k.toNat < inp.length → st1.mem (p+k) = BitVec.ofNat 8 (inp[k.toNat]!) := by
        intro k hk; rw [hbmem, hs0mem]; exact hbridge k hk
      have eout : regionBytes st1.mem q olen = produced := by rw [hbmem, hs0mem]; exact hout
      obtain ⟨F, s', status, outlen, her, hbr'⟩ :=
        ih (inp.length - (idx + 1 + commentSkip (inp.drop (idx+1)))) (by omega)
          (idx + 1 + commentSkip (inp.drop (idx+1))) olen st1 produced
          [.const ((BitVec.ofNat 64 idx + 1) + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))),
            .const (BitVec.ofNat 64 olen)] rfl hev' hr1 (by omega) holen holenp ebridge eout
      have hstep : Hex0.decodeS .High (inp.drop idx)
          = Hex0.decodeS .High (inp.drop (idx + 1 + commentSkip (inp.drop (idx+1)))) := by
        rw [hdropc, decodeS_high_comment _ _ hisCt, ← decodeS_comment_reconcile,
            show (inp.drop (idx+1)).drop (commentSkip (inp.drop (idx+1)))
              = inp.drop (idx + 1 + commentSkip (inp.drop (idx+1))) from by rw [List.drop_drop]]
      refine ⟨max fb F + 1, s', status, outlen, ?_, ?_⟩
      · show exec env sl (max fb F + 1) (hex0WhileS inits) s = _
        rw [hex0WhileS, exec_while_cont0 (hlen := hlen) (hs0 := hs0) (hc := hcond)
              (hb := exec_mono_le env sl (Nat.le_max_left fb F) heb) (hvs := rfl)]
        rw [show ([(BitVec.ofNat 64 idx + 1) + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1))),
              BitVec.ofNat 64 olen].map Opnd.const)
            = [Opnd.const ((BitVec.ofNat 64 idx + 1) + BitVec.ofNat 64 (commentSkip (inp.drop (idx+1)))),
              Opnd.const (BitVec.ofNat 64 olen)] from rfl]
        exact exec_mono_le env sl (Nat.le_max_right fb F) her
      · rw [hstep]; exact hbr'
    · -- HEX: hex-digit dispatch
      have hisCf : Hex0.isComment inp[idx]! = false := by
        unfold Hex0.isComment Hex0.c_hash Hex0.c_semi
        rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]; omega
      have hisSf : Hex0.isSpace inp[idx]! = false := by
        unfold Hex0.isSpace Hex0.c_nl Hex0.c_sp Hex0.c_us
        rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne,
            beq_eq_false_iff_ne]; omega
      have hns' : (s.mem (p + BitVec.ofNat 64 idx)).toNat ≠ 10 ∧ (s.mem (p + BitVec.ofNat 64 idx)).toNat ≠ 32
          ∧ (s.mem (p + BitVec.ofNat 64 idx)).toNat ≠ 95 ∧ (s.mem (p + BitVec.ofNat 64 idx)).toNat ≠ 35
          ∧ (s.mem (p + BitVec.ofNat 64 idx)).toNat ≠ 59 := by rw [hcv]; exact hns
      have hidx1 : idx + 1 < 2^64 := by omega
      have hpref_regs : RegsS (prefSt s0 p (BitVec.ofNat 64 idx)) p (BitVec.ofNat 64 inp.length) q
          (BitVec.ofNat 64 capN) := hr_s0.pref _
      have hpref6 : (prefSt s0 p (BitVec.ofNat 64 idx)).rget 6 = BitVec.ofNat 64 olen := by
        rw [prefSt_rget_pres _ _ _ _ (by decide) (by decide) (by decide)]; exact hs0_6
      have hpref41 : (prefSt s0 p (BitVec.ofNat 64 idx)).rget 41 = BitVec.ofNat 64 (idx+1) := by
        rw [prefSt_rget_41, ofNat_succ]
      have hpref7 : (prefSt s0 p (BitVec.ofNat 64 idx)).rget 7 = (s.mem (p + BitVec.ofNat 64 idx)).setWidth 64 := by
        rw [prefSt_rget_7, hs0mem]
      have hpm : (prefSt s0 p (BitVec.ofNat 64 idx)).mem = s.mem := by rw [prefSt_mem, hs0mem]
      rcases hexPathS_eff env sl (prefSt s0 p (BitVec.ofNat 64 idx)) p (BitVec.ofNat 64 inp.length) q
          (BitVec.ofNat 64 capN) (BitVec.ofNat 64 olen) idx (s.mem (p + BitVec.ofNat 64 idx))
          hpref_regs hpref6 hpref41 hpref7 hidx1 with
        ⟨hbad, fb, st1, hx, hsm⟩
        | ⟨hbad, hodd, fb, st1, hx, hsm⟩
        | ⟨hbad, hlt2, hls, fb, st1, hx, hsm⟩
        | ⟨hbad, hlt2, hnls, hbad2, fb, st1, hx, hsm⟩
        | ⟨hbad, hlt2, hnls, hbad2, hfull, fb, st1, hx, hsm⟩
        | ⟨hbad, hlt2, hnls, hbad2, holt, fb, st1, hx, hsm⟩
      · -- ARM A: bad high nibble → Unknown (5)
        obtain ⟨fB, heb⟩ := body_hex_lift env sl s0 p (BitVec.ofNat 64 inp.length) q
          (BitVec.ofNat 64 capN) (BitVec.ofNat 64 idx) (s.mem (p + BitVec.ofNat 64 idx)) st1
          (.ret [BitVec.ofNat 64 5, BitVec.ofNat 64 olen]) hr_s0 hs0_10 hs0_5 hchar0 hns'
          (catch0_ret _ _ _) ⟨fb, hx⟩
        have hnibn : Hex0.nibble inp[idx]! = none := by rw [← hcv]; exact (pnibR_eq_255_iff _).mp hbad
        have hdec : Hex0.decodeS .High (inp.drop idx) = ([], .Unknown) := by
          rw [hdropc]; exact decodeS_high_badhi _ _ hisCf hisSf hnibn
        have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
            (Hex0.decodeS .High (inp.drop idx)).2 capN = (5, produced, produced.length) := by
          rw [hdec]; simp [boundedRun, hpc, Hex0.statusCode]
        have hsmem : st1.mem = s.mem := by rw [hsm, prefSt_mem, hs0mem]
        refine ⟨fB + 1, st1, 5, olen, ?_, ?_⟩
        · show exec env sl (fB + 1) (hex0WhileS inits) s = _
          rw [hex0WhileS, exec_while_ret (hlen := hlen) (hs0 := hs0) (hc := hcond) (hb := heb)]
        · rw [hbr, hsmem, hout, holenp]
      · -- ARM B: input exhausted → OddEnd (4)
        have hnib : Hex0.nibble inp[idx]! = some (pnibR (s.mem (p + BitVec.ofNat 64 idx))).toNat := by
          rw [← hcv]; exact pnibR_nibble _ hbad
        obtain ⟨fB, heb⟩ := body_hex_lift env sl s0 p (BitVec.ofNat 64 inp.length) q
          (BitVec.ofNat 64 capN) (BitVec.ofNat 64 idx) (s.mem (p + BitVec.ofNat 64 idx)) st1
          (.ret [BitVec.ofNat 64 4, BitVec.ofNat 64 olen]) hr_s0 hs0_10 hs0_5 hchar0 hns'
          (catch0_ret _ _ _) ⟨fb, hx⟩
        have hrestnil : inp.drop (idx+1) = [] := by
          rw [List.drop_eq_nil_iff]; rw [tn inp.length (by omega)] at hodd; omega
        have hdec : Hex0.decodeS .High (inp.drop idx) = ([], .Trailing) := by
          rw [hdropc, decodeS_high_goodhi _ _ _ hisCf hisSf hnib, hrestnil, decodeS_low_nil]
        have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
            (Hex0.decodeS .High (inp.drop idx)).2 capN = (4, produced, produced.length) := by
          rw [hdec]; simp [boundedRun, hpc, Hex0.statusCode]
        have hsmem : st1.mem = s.mem := by rw [hsm, prefSt_mem, hs0mem]
        refine ⟨fB + 1, st1, 4, olen, ?_, ?_⟩
        · show exec env sl (fB + 1) (hex0WhileS inits) s = _
          rw [hex0WhileS, exec_while_ret (hlen := hlen) (hs0 := hs0) (hc := hcond) (hb := heb)]
        · rw [hbr, hsmem, hout, holenp]
      · -- ARM C: low-stop char → Split (3)
        have hnib : Hex0.nibble inp[idx]! = some (pnibR (s.mem (p + BitVec.ofNat 64 idx))).toNat := by
          rw [← hcv]; exact pnibR_nibble _ hbad
        rw [hpm] at hls
        obtain ⟨fB, heb⟩ := body_hex_lift env sl s0 p (BitVec.ofNat 64 inp.length) q
          (BitVec.ofNat 64 capN) (BitVec.ofNat 64 idx) (s.mem (p + BitVec.ofNat 64 idx)) st1
          (.ret [BitVec.ofNat 64 3, BitVec.ofNat 64 olen]) hr_s0 hs0_10 hs0_5 hchar0 hns'
          (catch0_ret _ _ _) ⟨fb, hx⟩
        have hlt2n : idx + 1 < inp.length := by rw [tn inp.length (by omega)] at hlt2; exact hlt2
        have hc2v : (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat = inp[idx+1]! := by
          have hb := hbridge (BitVec.ofNat 64 (idx+1)) (by rw [tn _ (by omega)]; exact hlt2n)
          rw [tn _ (by omega)] at hb
          rw [hb, BitVec.toNat_ofNat]
          have : inp[idx+1]! = inp[idx+1] := by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
          rw [this]; have := hinp _ (List.getElem_mem hlt2n); omega
        have hlsT : Hex0.isLowStop inp[idx+1]! = true := by rw [← hc2v]; exact (lowStop_iff _).mp hls
        have hdrop1 : inp.drop (idx+1) = inp[idx+1]! :: inp.drop (idx+2) := by
          rw [List.drop_eq_getElem_cons hlt2n]; congr 1
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
        have hdec : Hex0.decodeS .High (inp.drop idx) = ([], .Split) := by
          rw [hdropc, decodeS_high_goodhi _ _ _ hisCf hisSf hnib, hdrop1, decodeS_low_split _ _ _ hlsT]
        have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
            (Hex0.decodeS .High (inp.drop idx)).2 capN = (3, produced, produced.length) := by
          rw [hdec]; simp [boundedRun, hpc, Hex0.statusCode]
        have hsmem : st1.mem = s.mem := by rw [hsm, prefSt_mem, hs0mem]
        refine ⟨fB + 1, st1, 3, olen, ?_, ?_⟩
        · show exec env sl (fB + 1) (hex0WhileS inits) s = _
          rw [hex0WhileS, exec_while_ret (hlen := hlen) (hs0 := hs0) (hc := hcond) (hb := heb)]
        · rw [hbr, hsmem, hout, holenp]
      · -- ARM D: bad low nibble → Unknown (5)
        have hnib : Hex0.nibble inp[idx]! = some (pnibR (s.mem (p + BitVec.ofNat 64 idx))).toNat := by
          rw [← hcv]; exact pnibR_nibble _ hbad
        rw [hpm] at hnls hbad2
        obtain ⟨fB, heb⟩ := body_hex_lift env sl s0 p (BitVec.ofNat 64 inp.length) q
          (BitVec.ofNat 64 capN) (BitVec.ofNat 64 idx) (s.mem (p + BitVec.ofNat 64 idx)) st1
          (.ret [BitVec.ofNat 64 5, BitVec.ofNat 64 olen]) hr_s0 hs0_10 hs0_5 hchar0 hns'
          (catch0_ret _ _ _) ⟨fb, hx⟩
        have hlt2n : idx + 1 < inp.length := by rw [tn inp.length (by omega)] at hlt2; exact hlt2
        have hc2v : (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat = inp[idx+1]! := by
          have hb := hbridge (BitVec.ofNat 64 (idx+1)) (by rw [tn _ (by omega)]; exact hlt2n)
          rw [tn _ (by omega)] at hb
          rw [hb, BitVec.toNat_ofNat]
          have : inp[idx+1]! = inp[idx+1] := by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
          rw [this]; have := hinp _ (List.getElem_mem hlt2n); omega
        have hlsF : Hex0.isLowStop inp[idx+1]! = false := by
          rcases Bool.eq_false_or_eq_true (Hex0.isLowStop inp[idx+1]!) with h | h
          · exact absurd ((lowStop_iff _).mpr (by rw [hc2v]; exact h)) hnls
          · exact h
        have hnib2 : Hex0.nibble inp[idx+1]! = none := by rw [← hc2v]; exact (pnibR_eq_255_iff _).mp hbad2
        have hdrop1 : inp.drop (idx+1) = inp[idx+1]! :: inp.drop (idx+2) := by
          rw [List.drop_eq_getElem_cons hlt2n]; congr 1
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
        have hdec : Hex0.decodeS .High (inp.drop idx) = ([], .Unknown) := by
          rw [hdropc, decodeS_high_goodhi _ _ _ hisCf hisSf hnib, hdrop1, decodeS_low_badlo _ _ _ hlsF hnib2]
        have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
            (Hex0.decodeS .High (inp.drop idx)).2 capN = (5, produced, produced.length) := by
          rw [hdec]; simp [boundedRun, hpc, Hex0.statusCode]
        have hsmem : st1.mem = s.mem := by rw [hsm, prefSt_mem, hs0mem]
        refine ⟨fB + 1, st1, 5, olen, ?_, ?_⟩
        · show exec env sl (fB + 1) (hex0WhileS inits) s = _
          rw [hex0WhileS, exec_while_ret (hlen := hlen) (hs0 := hs0) (hc := hcond) (hb := heb)]
        · rw [hbr, hsmem, hout, holenp]
      · -- ARM E: output full → OutputShort (2)
        have hnib : Hex0.nibble inp[idx]! = some (pnibR (s.mem (p + BitVec.ofNat 64 idx))).toNat := by
          rw [← hcv]; exact pnibR_nibble _ hbad
        rw [hpm] at hnls hbad2
        obtain ⟨fB, heb⟩ := body_hex_lift env sl s0 p (BitVec.ofNat 64 inp.length) q
          (BitVec.ofNat 64 capN) (BitVec.ofNat 64 idx) (s.mem (p + BitVec.ofNat 64 idx)) st1
          (.ret [BitVec.ofNat 64 2, BitVec.ofNat 64 olen]) hr_s0 hs0_10 hs0_5 hchar0 hns'
          (catch0_ret _ _ _) ⟨fb, hx⟩
        have hlt2n : idx + 1 < inp.length := by rw [tn inp.length (by omega)] at hlt2; exact hlt2
        have hc2v : (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat = inp[idx+1]! := by
          have hb := hbridge (BitVec.ofNat 64 (idx+1)) (by rw [tn _ (by omega)]; exact hlt2n)
          rw [tn _ (by omega)] at hb
          rw [hb, BitVec.toNat_ofNat]
          have : inp[idx+1]! = inp[idx+1] := by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
          rw [this]; have := hinp _ (List.getElem_mem hlt2n); omega
        have hlsF : Hex0.isLowStop inp[idx+1]! = false := by
          rcases Bool.eq_false_or_eq_true (Hex0.isLowStop inp[idx+1]!) with h | h
          · exact absurd ((lowStop_iff _).mpr (by rw [hc2v]; exact h)) hnls
          · exact h
        have hnib2 : Hex0.nibble inp[idx+1]! = some (pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))).toNat := by
          rw [← hc2v]; exact pnibR_nibble _ hbad2
        have hcapeq : produced.length = capN := by
          rw [tn capN (by omega), tn olen (by omega)] at hfull; omega
        have hdrop1 : inp.drop (idx+1) = inp[idx+1]! :: inp.drop (idx+2) := by
          rw [List.drop_eq_getElem_cons hlt2n]; congr 1
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
        have hdec : Hex0.decodeS .High (inp.drop idx)
            = (((pnibR (s.mem (p + BitVec.ofNat 64 idx))).toNat * 16
                + (pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))).toNat)
                  :: (Hex0.decodeS .High (inp.drop (idx+2))).1, (Hex0.decodeS .High (inp.drop (idx+2))).2) := by
          rw [hdropc, decodeS_high_goodhi _ _ _ hisCf hisSf hnib, hdrop1, decodeS_low_goodlo _ _ _ _ hlsF hnib2]
        have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
            (Hex0.decodeS .High (inp.drop idx)).2 capN = (2, produced, capN) := by
          rw [hdec]; unfold boundedRun
          rw [if_neg (by simp only [List.length_cons]; omega)]
          simp [show capN - produced.length = 0 from by omega]
        have hsmem : st1.mem = s.mem := by rw [hsm, prefSt_mem, hs0mem]
        refine ⟨fB + 1, st1, 2, olen, ?_, ?_⟩
        · show exec env sl (fB + 1) (hex0WhileS inits) s = _
          rw [hex0WhileS, exec_while_ret (hlen := hlen) (hs0 := hs0) (hc := hcond) (hb := heb)]
        · rw [hbr, hsmem, hout, holenp, hcapeq]
      · -- ARM F: write the byte, continue
        have hnib : Hex0.nibble inp[idx]! = some (pnibR (s.mem (p + BitVec.ofNat 64 idx))).toNat := by
          rw [← hcv]; exact pnibR_nibble _ hbad
        rw [hpm] at hnls hbad2 hsm
        have hlt2n : idx + 1 < inp.length := by rw [tn inp.length (by omega)] at hlt2; exact hlt2
        have holt' : olen < capN := by rw [tn olen (by omega), tn capN (by omega)] at holt; exact holt
        have hc2v : (s.mem (p + BitVec.ofNat 64 (idx+1))).toNat = inp[idx+1]! := by
          have hb := hbridge (BitVec.ofNat 64 (idx+1)) (by rw [tn _ (by omega)]; exact hlt2n)
          rw [tn _ (by omega)] at hb
          rw [hb, BitVec.toNat_ofNat]
          have : inp[idx+1]! = inp[idx+1] := by simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
          rw [this]; have := hinp _ (List.getElem_mem hlt2n); omega
        have hlsF : Hex0.isLowStop inp[idx+1]! = false := by
          rcases Bool.eq_false_or_eq_true (Hex0.isLowStop inp[idx+1]!) with h | h
          · exact absurd ((lowStop_iff _).mpr (by rw [hc2v]; exact h)) hnls
          · exact h
        have hnib2 : Hex0.nibble inp[idx+1]! = some (pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))).toNat := by
          rw [← hc2v]; exact pnibR_nibble _ hbad2
        have hdrop1 : inp.drop (idx+1) = inp[idx+1]! :: inp.drop (idx+2) := by
          rw [List.drop_eq_getElem_cons hlt2n]; congr 1
          simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt2n]
        have hbyteval : (((pnibR (s.mem (p + BitVec.ofNat 64 idx)) <<< 4)
              ||| pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))).setWidth 8).toNat
            = (pnibR (s.mem (p + BitVec.ofNat 64 idx))).toNat * 16
                + (pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))).toNat := hexbyte_val _ _ hbad hbad2
        -- body result via lift
        obtain ⟨fB, heb⟩ := body_hex_lift env sl s0 p (BitVec.ofNat 64 inp.length) q
          (BitVec.ofNat 64 capN) (BitVec.ofNat 64 idx) (s.mem (p + BitVec.ofNat 64 idx)) st1
          (.cont 0 [BitVec.ofNat 64 (idx+1) + 1, BitVec.ofNat 64 olen + 1]) hr_s0 hs0_10 hs0_5 hchar0 hns'
          (catch0_cont _ _ _ _) ⟨fb, hx⟩
        have hr1 : RegsS st1 p (BitVec.ofNat 64 inp.length) q (BitVec.ofNat 64 capN) :=
          RegsS.frame env sl hr_s0 heb
        have ebridge : ∀ k : Word, k.toNat < inp.length → st1.mem (p+k) = BitVec.ofNat 8 (inp[k.toNat]!) := by
          intro k hk
          have hne : p + k ≠ q + BitVec.ofNat 64 olen := by
            intro heq; exact hdisj (p+k) ⟨k.toNat, hk, by bv_omega⟩ ⟨olen, holt', heq⟩
          rw [hsm, storeByte_mem_ne _ _ _ _ hne, hpm]; exact hbridge k hk
        have eout : regionBytes st1.mem q (olen+1)
            = produced ++ [(pnibR (s.mem (p + BitVec.ofNat 64 idx))).toNat * 16
                + (pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))).toNat] := by
          rw [hsm, regionBytes_snoc]
          congr 1
          · rw [regionBytes_storeByte_self _ _ _ _ (by omega), hpm, hout]
          · rw [storeByte_mem_self, hbyteval]
        have hev' : ([Opnd.const (BitVec.ofNat 64 (idx+1) + 1), Opnd.const (BitVec.ofNat 64 olen + 1)].map
              (evalOpnd st1)) = [BitVec.ofNat 64 (idx+2), BitVec.ofNat 64 (olen+1)] := by
          simp only [List.map_cons, evalOpnd_const, List.map_nil]
          rw [show BitVec.ofNat 64 (idx+1) + 1 = BitVec.ofNat 64 (idx+2) from by bv_omega,
              show BitVec.ofNat 64 olen + 1 = BitVec.ofNat 64 (olen+1) from by bv_omega]
        obtain ⟨F, s', status, outlen, her, hbr'⟩ :=
          ih (inp.length - (idx+2)) (by omega) (idx+2) (olen+1) st1
            (produced ++ [(pnibR (s.mem (p + BitVec.ofNat 64 idx))).toNat * 16
                + (pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))).toNat])
            [.const (BitVec.ofNat 64 (idx+1) + 1), .const (BitVec.ofNat 64 olen + 1)] rfl hev' hr1
            (by omega) (by omega) (by simp [holenp]) ebridge eout
        have hbreq : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
              (Hex0.decodeS .High (inp.drop idx)).2 capN
            = boundedRun (produced ++ [(pnibR (s.mem (p + BitVec.ofNat 64 idx))).toNat * 16
                + (pnibR (s.mem (p + BitVec.ofNat 64 (idx+1)))).toNat])
              (Hex0.decodeS .High (inp.drop (idx+2))).1 (Hex0.decodeS .High (inp.drop (idx+2))).2 capN := by
          rw [hdropc, decodeS_high_goodhi _ _ _ hisCf hisSf hnib, hdrop1, decodeS_low_goodlo _ _ _ _ hlsF hnib2]
          exact boundedRun_cons _ _ _ _ _ (by omega)
        refine ⟨max fB F + 1, s', status, outlen, ?_, ?_⟩
        · show exec env sl (max fB F + 1) (hex0WhileS inits) s = _
          rw [hex0WhileS, exec_while_cont0 (hlen := hlen) (hs0 := hs0) (hc := hcond)
                (hb := exec_mono_le env sl (Nat.le_max_left fB F) heb) (hvs := rfl)]
          rw [show ([BitVec.ofNat 64 (idx+1) + 1, BitVec.ofNat 64 olen + 1].map Opnd.const)
                = [Opnd.const (BitVec.ofNat 64 (idx+1) + 1), Opnd.const (BitVec.ofNat 64 olen + 1)] from rfl]
          exact exec_mono_le env sl (Nat.le_max_right fB F) her
        · rw [hbreq]; exact hbr'
  · -- base case: guard false, idx = |inp|
    have hidxlen : idx = inp.length := by omega
    have hcond : evalCond .lt (s0.rget 5) (s0.rget 11) = false := by
      rw [hs0_5, hs0_11]
      exact slt_false (by rw [tn idx (by omega)]; omega) (by rw [tn inp.length (by omega)]; omega)
        (by rw [tn inp.length (by omega), tn idx (by omega)]; omega)
    have hdflt : exec env sl (0+1) (.ret [.const 0, .reg 6]) s0
        = some (s0, .ret [0, BitVec.ofNat 64 olen]) := by
      rw [exec_ret]; simp only [List.map_cons, evalOpnd_const, evalOpnd_reg, List.map_nil, hs0_6]
    have hbr : boundedRun produced (Hex0.decodeS .High (inp.drop idx)).1
        (Hex0.decodeS .High (inp.drop idx)).2 capN = (0, produced, produced.length) := by
      rw [show inp.drop idx = [] from by rw [List.drop_eq_nil_iff]; omega, decodeS_high_nil]
      simp [boundedRun, hpc, Hex0.statusCode]
    refine ⟨0+1+1, s0, 0, olen, ?_, ?_⟩
    · show exec env sl (0+1+1) (hex0WhileS inits) s = _
      rw [hex0WhileS, exec_while_F_ret (hlen := hlen) (hs0 := hs0) (hc := hcond) (hb := hdflt),
          show (0 : Word) = BitVec.ofNat 64 0 from by decide]
    · rw [hbr, hs0mem, hout, holenp]

/-! ### Phase 6 — assembly: the whole `hex0S` against `Hex0.coreSpec`.

    `run`s the SSA `hex0S` on `memIn (asBytes inp)`: it returns exactly the
    `coreSpec` status and output length in its two `.ret` values, and the bytes
    it wrote to the output region `[outBase, outBase+len)` are `coreSpec`'s
    output. No `native_decide` — the axiom base is `[propext, Classical.choice,
    Quot.sound]`. -/
theorem hex0S_correct (inp : List Nat) (cap : Nat)
    (hinp : ∀ x ∈ inp, x < 256) (hlen : inp.length < 2^63) (hcap : cap < 2^63)
    (hdisj : Disjoint ⟨Lib.inBase, inp.length⟩ ⟨Lib.outBase, cap⟩) :
    ∃ fuel s', run Lib.libEnvS 0 fuel "hex0"
          [Lib.inBase, BitVec.ofNat 64 inp.length, Lib.outBase, BitVec.ofNat 64 cap]
          (Lib.memIn (Lib.asBytes inp)) Prog.SP0
        = some (s', [BitVec.ofNat 64 (Hex0.coreSpec inp cap).1,
                     BitVec.ofNat 64 (Hex0.coreSpec inp cap).2.2])
      ∧ regionBytes s'.mem Lib.outBase (Hex0.coreSpec inp cap).2.2 = (Hex0.coreSpec inp cap).2.1 := by
  -- frameEnter: frameSize 0, so it always succeeds; st0 holds the 4 params + mem
  have hcond : ¬ (Prog.SP0.toNat < (0 : Word).toNat + Lib.hex0S.frameSize) := by
    show ¬ (Prog.SP0.toNat < (0 : Word).toNat + 0); simp
  obtain ⟨st0, hfe⟩ : ∃ st0, frameEnter 0 Lib.hex0S
      [Lib.inBase, BitVec.ofNat 64 inp.length, Lib.outBase, BitVec.ofNat 64 cap]
      (Lib.memIn (Lib.asBytes inp)) Prog.SP0 = some st0 := by
    unfold frameEnter; rw [if_neg hcond]; exact ⟨_, rfl⟩
  have hst0_10 : st0.rget 10 = Lib.inBase := by
    have h := hfe; unfold frameEnter at h; rw [if_neg hcond] at h; rw [← Option.some.inj h]; rfl
  have hst0_11 : st0.rget 11 = BitVec.ofNat 64 inp.length := by
    have h := hfe; unfold frameEnter at h; rw [if_neg hcond] at h; rw [← Option.some.inj h]; rfl
  have hst0_12 : st0.rget 12 = Lib.outBase := by
    have h := hfe; unfold frameEnter at h; rw [if_neg hcond] at h; rw [← Option.some.inj h]; rfl
  have hst0_13 : st0.rget 13 = BitVec.ofNat 64 cap := by
    have h := hfe; unfold frameEnter at h; rw [if_neg hcond] at h; rw [← Option.some.inj h]; rfl
  have hst0mem : st0.mem = Lib.memIn (Lib.asBytes inp) := by
    have h := hfe; unfold frameEnter at h; rw [if_neg hcond] at h; rw [← Option.some.inj h]
  -- the 11-literal prelude → loop-entry state sb
  obtain ⟨sb, hsb⟩ : ∃ y, y = (((((((((((st0.rset 17 (BitVec.ofNat 64 55)).rset 18 (BitVec.ofNat 64 59)).rset
      19 (BitVec.ofNat 64 255)).rset 20 (BitVec.ofNat 64 48)).rset 21 (BitVec.ofNat 64 57)).rset
      22 (BitVec.ofNat 64 65)).rset 23 (BitVec.ofNat 64 70)).rset 24 (BitVec.ofNat 64 10)).rset
      25 (BitVec.ofNat 64 32)).rset 26 (BitVec.ofNat 64 95)).rset 27 (BitVec.ofNat 64 35)) := ⟨_, rfl⟩
  have hsbmem : sb.mem = Lib.memIn (Lib.asBytes inp) := by rw [hsb]; simp [hst0mem]
  have hr_sb : RegsS sb Lib.inBase (BitVec.ofNat 64 inp.length) Lib.outBase (BitVec.ofNat 64 cap) := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      (rw [hsb]; simp [hst0_10, hst0_11, hst0_12, hst0_13])
  -- bridge: memIn holds inp at inBase
  have hbridge : ∀ k : Word, k.toNat < inp.length → sb.mem (Lib.inBase + k) = BitVec.ofNat 8 (inp[k.toNat]!) := by
    intro k hk
    rw [hsbmem]
    have hia : ((Lib.inBase + k) - Lib.inBase).toNat = k.toNat := by bv_omega
    have hlen' : (Lib.asBytes inp).length = inp.length := by simp [Lib.asBytes]
    show (if ((Lib.inBase + k) - Lib.inBase).toNat < (Lib.asBytes inp).length
        then _ else _) = _
    rw [hia, hlen', if_pos hk, List.getElem?_eq_getElem (by rw [hlen']; exact hk)]
    simp [Lib.asBytes, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  -- run the main loop from idx = olen = 0
  obtain ⟨F, s', status, outlen, hF, hbr⟩ :=
    main_loop Lib.libEnvS 0 inp Lib.inBase Lib.outBase cap hinp hlen hcap hdisj
      (inp.length - 0) 0 0 sb [] [.const 0, .const 0] rfl (by rfl) hr_sb
      (by omega) (by omega) rfl hbridge (by simp [regionBytes])
  rw [List.drop_zero, boundedRun_nil_coreSpec] at hbr
  refine ⟨F + 12, s', ?_, ?_⟩
  · -- run: peel frameEnter + 11 lits, land on the loop, read the ret
    have hbody : exec Lib.libEnvS 0 (F+12) Lib.hex0S.body st0
        = some (s', .ret [BitVec.ofNat 64 status, BitVec.ofNat 64 outlen]) := by
      show exec Lib.libEnvS 0 (F+12)
        (.seq (Lib.lit 17 55) (.seq (Lib.lit 18 59) (.seq (Lib.lit 19 255) (.seq (Lib.lit 20 48)
          (.seq (Lib.lit 21 57) (.seq (Lib.lit 22 65) (.seq (Lib.lit 23 70) (.seq (Lib.lit 24 10)
          (.seq (Lib.lit 25 32) (.seq (Lib.lit 26 95) (.seq (Lib.lit 27 35)
            (hex0WhileS [.const 0, .const 0])))))))))))) st0 = _
      rw [show F+12 = (F+11)+1 from rfl, exec_seq_normal (h := exec_lit Lib.libEnvS 0 (F+10) 17 55 _ (by decide)),
          show F+11 = (F+10)+1 from rfl, exec_seq_normal (h := exec_lit Lib.libEnvS 0 (F+9) 18 59 _ (by decide)),
          show F+10 = (F+9)+1 from rfl, exec_seq_normal (h := exec_lit Lib.libEnvS 0 (F+8) 19 255 _ (by decide)),
          show F+9 = (F+8)+1 from rfl, exec_seq_normal (h := exec_lit Lib.libEnvS 0 (F+7) 20 48 _ (by decide)),
          show F+8 = (F+7)+1 from rfl, exec_seq_normal (h := exec_lit Lib.libEnvS 0 (F+6) 21 57 _ (by decide)),
          show F+7 = (F+6)+1 from rfl, exec_seq_normal (h := exec_lit Lib.libEnvS 0 (F+5) 22 65 _ (by decide)),
          show F+6 = (F+5)+1 from rfl, exec_seq_normal (h := exec_lit Lib.libEnvS 0 (F+4) 23 70 _ (by decide)),
          show F+5 = (F+4)+1 from rfl, exec_seq_normal (h := exec_lit Lib.libEnvS 0 (F+3) 24 10 _ (by decide)),
          show F+4 = (F+3)+1 from rfl, exec_seq_normal (h := exec_lit Lib.libEnvS 0 (F+2) 25 32 _ (by decide)),
          show F+3 = (F+2)+1 from rfl, exec_seq_normal (h := exec_lit Lib.libEnvS 0 (F+1) 26 95 _ (by decide)),
          show F+2 = (F+1)+1 from rfl, exec_seq_normal (h := exec_lit Lib.libEnvS 0 F 27 35 _ (by decide))]
      rw [← hsb]; exact exec_mono_le Lib.libEnvS 0 (Nat.le_succ F) hF
    show run Lib.libEnvS 0 (F+12) "hex0" _ _ _ = _
    unfold run
    rw [show List.lookup "hex0" Lib.libEnvS = some Lib.hex0S from rfl]
    simp only [List.length_cons, List.length_nil, hfe, hbody]
    rw [← hbr]; rfl
  · rw [← hbr]

end LowIR.SSA
