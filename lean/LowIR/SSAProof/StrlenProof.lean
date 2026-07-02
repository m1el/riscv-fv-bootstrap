/-
  LowIR.SSAProof.StrlenProof — Phase 1 of the hex0-on-SSA campaign
  (docs/RESUME-SSA-HEX0.md §Phase 1): the `strlenS` vertical slice, the GO/NO-GO
  on the args-tuple loop invariant.

  This is the smallest SSA loop with a loop-carried result: args `(6, 7) =
  (cursor, byte-at-cursor)`, the guard-false `dflt` computes the length from the
  final cursor. The point of the slice is to exercise the WHOLE Phase-0 pipeline
  once — `exec_while_cont0` / `exec_while_F_brk0`, the args-tuple invariant, the
  frame theorem, `exec_mono_le` for fuel reconciliation, `run`-level assembly —
  before paying hex0 prices.

  Headline contrast with the flat `LowIR.StrlenProof`: the loop invariant is a
  statement about the args tuple `(cur, byte)`, not about a mutable register
  file; `cur` and `byte` are the loop *arguments*, reissued by `cont 0`.
-/
import LowIR.SSAProof.ExecFacts
import LowIR.SSALib

namespace LowIR.SSA

open LowIR (Cond evalCond)
open Rv64i (Word Byte)

variable (env : Env) (sl : Word)

/-! ### The `strlenS` loop pieces (must match `SSA.Lib.strlenS`). -/

def slBody : Stmt := .seq (.addi 8 6 1) (.seq (.lbu 9 8 0) (.cont 0 [.reg 8, .reg 9]))
def slDflt : Stmt := .seq (.sub 13 6 10) (.brk 0 [.reg 13])
def slWhile (inits : List Opnd) : Stmt := .«while» [12] inits [6, 7] .geu 7 16 slBody slDflt

/-! ### Arithmetic / condition facts. -/

theorem one_signExtend : (1 : BitVec 12).signExtend 64 = (1 : Word) := by decide
theorem zero_signExtend : (0 : BitVec 12).signExtend 64 = (0 : Word) := by decide
theorem wadd_zero (x : Word) : x + (0 : Word) = x := by bv_omega
theorem cur_zero (cur : Word) : cur + BitVec.ofNat 64 0 = cur := by bv_omega
theorem cur_step (cur : Word) (k : Nat) :
    cur + BitVec.ofNat 64 (k+1) = (cur + 1) + BitVec.ofNat 64 k := by bv_omega

/-- Loop guard `byte ≥u 1` is true exactly when the byte is non-NUL. -/
theorem geu_one_true (b : Byte) (h : b ≠ 0) : evalCond .geu (b.setWidth 64) 1 = true := by
  have hbn : b.toNat ≠ 0 := fun hh => h (by bv_omega)
  have hsw : (b.setWidth 64).toNat = b.toNat := by
    rw [BitVec.toNat_setWidth]; have := b.isLt; omega
  have h1 : (1 : Word).toNat = 1 := by decide
  have hult : (b.setWidth 64).ult 1 = false := by
    have e : (b.setWidth 64).ult 1 = decide ((b.setWidth 64).toNat < (1 : Word).toNat) := rfl
    rw [e, hsw, h1]; exact decide_eq_false (by omega)
  simp only [evalCond, hult, Bool.not_false]

theorem geu_one_false : evalCond .geu ((0 : Byte).setWidth 64) 1 = false := by decide

/-! ### Body / dflt execution (small, so run them explicitly). -/

/-- One loop body: advance the cursor, load the next byte, `cont 0` the pair. -/
theorem slBody_exec (s0 : St) (cur : Word) (h6 : s0.rget 6 = cur) :
    exec env sl 3 slBody s0
      = some ((s0.rset 8 (cur + 1)).rset 9 ((s0.mem (cur + 1)).setWidth 64),
              .cont 0 [cur + 1, (s0.mem (cur + 1)).setWidth 64]) := by
  have ha : exec env sl 2 (.addi 8 6 1) s0 = some (s0.rset 8 (cur + 1), .normal) := by
    rw [show (2:Nat) = 1+1 from rfl, exec_addi, h6, one_signExtend]
  have hl : exec env sl 1 (.lbu 9 8 0) (s0.rset 8 (cur + 1))
      = some ((s0.rset 8 (cur + 1)).rset 9 ((s0.mem (cur + 1)).setWidth 64), .normal) := by
    rw [show (1:Nat) = 0+1 from rfl, exec_lbu]
    simp only [rget_rset_eq _ 8 _ (by decide), zero_signExtend, wadd_zero, loadByte_eq, rset_mem]
  show exec env sl (2+1) (.seq (.addi 8 6 1) (.seq (.lbu 9 8 0) (.cont 0 [.reg 8, .reg 9]))) s0 = _
  rw [exec_seq_normal (h := ha), show (2:Nat) = 1+1 from rfl, exec_seq_normal (h := hl), exec_cont]
  simp

/-- Guard-false path: length = cursor − base, delivered by `brk 0`. -/
theorem slDflt_exec (s0 : St) (cur p : Word) (h6 : s0.rget 6 = cur) (h10 : s0.rget 10 = p) :
    exec env sl 2 slDflt s0 = some (s0.rset 13 (cur - p), .brk 0 [cur - p]) := by
  have hs : exec env sl 1 (.sub 13 6 10) s0 = some (s0.rset 13 (cur - p), .normal) := by
    rw [show (1:Nat) = 0+1 from rfl, exec_sub, h6, h10]
  show exec env sl (1+1) (.seq (.sub 13 6 10) (.brk 0 [.reg 13])) s0 = _
  rw [exec_seq_normal (h := hs), exec_brk]; simp

/-! ### The loop lemma — args-tuple invariant, induction on the distance to NUL,
    existential fuel reconciled with `exec_mono_le`. -/

theorem strlen_loop (p : Word) (n : Nat) :
    ∀ (s : St) (cur : Word) (inits : List Opnd),
      inits.map (evalOpnd s) = [cur, (s.mem cur).setWidth 64] →
      s.rget 16 = 1 → s.rget 10 = p →
      (∀ k, k < n → s.mem (cur + BitVec.ofNat 64 k) ≠ 0) →
      s.mem (cur + BitVec.ofNat 64 n) = 0 →
      ∃ F s', exec env sl F (slWhile inits) s = some (s', .normal)
        ∧ s'.rget 12 = (cur + BitVec.ofNat 64 n) - p
        ∧ s'.mem = s.mem := by
  induction n with
  | zero =>
    intro s cur inits hev h16 h10 _ hz
    rw [cur_zero] at hz
    have hlen : inits.length = [6, 7].length := by
      have := congrArg List.length hev; simpa using this
    obtain ⟨s0, hs0⟩ : ∃ y, y = bindOuts s [6, 7] (inits.map (evalOpnd s)) := ⟨_, rfl⟩
    have hbo : s0 = (s.rset 6 cur).rset 7 ((s.mem cur).setWidth 64) := by rw [hs0, hev]; rfl
    have hg7 : s0.rget 7 = (s.mem cur).setWidth 64 := by rw [hbo]; simp
    have hg16 : s0.rget 16 = 1 := by rw [hbo]; simp [h16]
    have hg6 : s0.rget 6 = cur := by rw [hbo]; simp
    have hg10 : s0.rget 10 = p := by rw [hbo]; simp [h10]
    have hcond : evalCond .geu (s0.rget 7) (s0.rget 16) = false := by
      rw [hg7, hg16, hz]; exact geu_one_false
    refine ⟨3, (s0.rset 13 (cur - p)).rset 12 (cur - p), ?_, ?_, ?_⟩
    · show exec env sl (2 + 1) (slWhile inits) s = _
      rw [slWhile, exec_while_F_brk0 (hlen := hlen) (hs0 := hs0) (hc := hcond)
            (hb := slDflt_exec env sl s0 cur p hg6 hg10) (hvs := rfl)]
      rfl
    · simp
    · rw [hbo]; simp
  | succ n ih =>
    intro s cur inits hev h16 h10 hpre hz
    have hlen : inits.length = [6, 7].length := by
      have := congrArg List.length hev; simpa using this
    obtain ⟨s0, hs0⟩ : ∃ y, y = bindOuts s [6, 7] (inits.map (evalOpnd s)) := ⟨_, rfl⟩
    have hbo : s0 = (s.rset 6 cur).rset 7 ((s.mem cur).setWidth 64) := by rw [hs0, hev]; rfl
    have hg7 : s0.rget 7 = (s.mem cur).setWidth 64 := by rw [hbo]; simp
    have hg16 : s0.rget 16 = 1 := by rw [hbo]; simp [h16]
    have hg6 : s0.rget 6 = cur := by rw [hbo]; simp
    have hg10 : s0.rget 10 = p := by rw [hbo]; simp [h10]
    have hmem0 : s0.mem = s.mem := by rw [hbo]; simp
    have hb0 : s.mem cur ≠ 0 := by have := hpre 0 (by omega); rwa [cur_zero] at this
    have hcond : evalCond .geu (s0.rget 7) (s0.rget 16) = true := by
      rw [hg7, hg16]; exact geu_one_true _ hb0
    obtain ⟨s1, hs1⟩ : ∃ y, y = (s0.rset 8 (cur + 1)).rset 9 ((s0.mem (cur + 1)).setWidth 64) :=
      ⟨_, rfl⟩
    have hbody : exec env sl 3 slBody s0
        = some (s1, .cont 0 [cur + 1, (s0.mem (cur + 1)).setWidth 64]) := by
      rw [hs1]; exact slBody_exec env sl s0 cur hg6
    have hs1mem : s1.mem = s.mem := by rw [hs1]; simp [hmem0]
    have hs1_16 : s1.rget 16 = 1 := by rw [hs1]; simp [hg16]
    have hs1_10 : s1.rget 10 = p := by rw [hs1]; simp [hg10]
    have hmemcur1 : s0.mem (cur + 1) = s.mem (cur + 1) := by rw [hmem0]
    have hev' : ([Opnd.const (cur + 1), Opnd.const ((s0.mem (cur + 1)).setWidth 64)].map
          (evalOpnd s1)) = [cur + 1, (s1.mem (cur + 1)).setWidth 64] := by
      simp only [List.map_cons, evalOpnd_const, List.map_nil, hs1mem, hmemcur1]
    have hpre' : ∀ k, k < n → s1.mem ((cur + 1) + BitVec.ofNat 64 k) ≠ 0 := by
      intro k hk; rw [hs1mem, ← cur_step]; exact hpre (k + 1) (by omega)
    have hz' : s1.mem ((cur + 1) + BitVec.ofNat 64 n) = 0 := by
      rw [hs1mem, ← cur_step]; exact hz
    obtain ⟨F, s', hF, h12, hmem⟩ := ih s1 (cur + 1) _ hev' hs1_16 hs1_10 hpre' hz'
    refine ⟨max 3 F + 1, s', ?_, ?_, ?_⟩
    · show exec env sl (max 3 F + 1) (slWhile inits) s = _
      rw [slWhile, exec_while_cont0 (hlen := hlen) (hs0 := hs0) (hc := hcond)
            (hb := exec_mono_le env sl (Nat.le_max_left 3 F) hbody) (hvs := rfl)]
      rw [show ([cur + 1, (s0.mem (cur + 1)).setWidth 64].map Opnd.const)
            = [Opnd.const (cur + 1), Opnd.const ((s0.mem (cur + 1)).setWidth 64)] from rfl]
      exact exec_mono_le env sl (Nat.le_max_right 3 F) hF
    · rw [h12, cur_step]
    · rw [hmem, hs1mem]

/-! ### `run`-level assembly — the whole `strlenS` against the string spec. -/

/-- `n` is the length of the NUL-terminated string at `p`: byte `n` is NUL, every
    earlier byte non-NUL (same shape as the flat `LowIR.StrlenProof.IsLen`). -/
def IsLen (mem : Word → Byte) (p : Word) (n : Nat) : Prop :=
  mem (p + BitVec.ofNat 64 n) = 0 ∧ ∀ k, k < n → mem (p + BitVec.ofNat 64 k) ≠ 0

/-- **strlenS is correct.** With `p` in x10 and the first NUL at offset `n`, the
    SSA `strlenS` returns the length `n` as the sole `.ret` value. -/
theorem strlenS_correct (mem : Word → Byte) (p sp : Word) (n : Nat)
    (hlk : List.lookup "strlen" env = some Lib.strlenS)
    (hsp : sl.toNat ≤ sp.toNat) (hlen : IsLen mem p n) :
    ∃ F s', run env sl F "strlen" [p] mem sp = some (s', [BitVec.ofNat 64 n]) := by
  obtain ⟨hnul, hpre⟩ := hlen
  -- frameEnter: frameSize 0, so it always succeeds; st0 holds p in x10, mem, sp
  have hcond : ¬ sp.toNat < sl.toNat + Lib.strlenS.frameSize := by
    show ¬ sp.toNat < sl.toNat + 0; omega
  obtain ⟨st0, hfe⟩ : ∃ st0, frameEnter sl Lib.strlenS [p] mem sp = some st0 := by
    unfold frameEnter; rw [if_neg hcond]; exact ⟨_, rfl⟩
  have hst0_10 : st0.rget 10 = p := by
    have h := hfe; unfold frameEnter at h; rw [if_neg hcond] at h; rw [← Option.some.inj h]; rfl
  have hst0_mem : st0.mem = mem := by
    have h := hfe; unfold frameEnter at h; rw [if_neg hcond] at h; rw [← Option.some.inj h]
  -- run the two preamble instructions to the loop-entry state sb
  obtain ⟨sa, hsa⟩ : ∃ y, y = st0.rset 5 ((st0.mem p).setWidth 64) := ⟨_, rfl⟩
  obtain ⟨sb, hsb⟩ : ∃ y, y = sa.rset 16 1 := ⟨_, rfl⟩
  have hsb10 : sb.rget 10 = p := by rw [hsb, hsa]; simp [hst0_10]
  have hsb16 : sb.rget 16 = 1 := by rw [hsb]; simp
  have hsbmem : sb.mem = mem := by rw [hsb, hsa]; simp [hst0_mem]
  have hsb5 : sb.rget 5 = (mem p).setWidth 64 := by rw [hsb, hsa]; simp [hst0_mem]
  have hev : ([Opnd.reg 10, Opnd.reg 5].map (evalOpnd sb)) = [p, (sb.mem p).setWidth 64] := by
    simp only [List.map_cons, evalOpnd_reg, List.map_nil, hsb10, hsb5, hsbmem]
  obtain ⟨F, s', hF, h12, _⟩ :=
    strlen_loop env sl p n sb p [.reg 10, .reg 5] hev hsb16 hsb10
      (fun k hk => by rw [hsbmem]; exact hpre k hk) (by rw [hsbmem]; exact hnul)
  have h12n : s'.rget 12 = BitVec.ofNat 64 n := by rw [h12]; bv_omega
  refine ⟨F + 4, s', ?_⟩
  -- preamble (2) + loop (bumped to fuel F+1) + ret (1) = fuel F+4 on the body
  have hbody : exec env sl (F + 4) Lib.strlenS.body st0
      = some (s', .ret [BitVec.ofNat 64 n]) := by
    show exec env sl (F + 4)
      (.seq (.lbu 5 10 0) (.seq (.addi 16 0 (BitVec.ofNat 12 1))
        (.seq (slWhile [.reg 10, .reg 5]) (.ret [.reg 12])))) st0 = _
    have e1 : exec env sl (F + 3) (.lbu 5 10 0) st0 = some (sa, .normal) := by
      rw [show F + 3 = (F + 2) + 1 from rfl, exec_lbu, hst0_10, hsa]; simp
    have e2 : exec env sl (F + 2) (.addi 16 0 (BitVec.ofNat 12 1)) sa = some (sb, .normal) := by
      have hv : sa.rget 0 + (BitVec.ofNat 12 1).signExtend 64 = (1 : Word) := by rw [rget_zero]; decide
      rw [show F + 2 = (F + 1) + 1 from rfl, exec_addi, hv, hsb]
    have eloop : exec env sl (F + 1) (slWhile [.reg 10, .reg 5]) sb = some (s', .normal) :=
      exec_mono_le env sl (Nat.le_succ F) hF
    rw [show F + 4 = (F + 3) + 1 from rfl, exec_seq_normal (h := e1),
        show F + 3 = (F + 2) + 1 from rfl, exec_seq_normal (h := e2),
        show F + 2 = (F + 1) + 1 from rfl, exec_seq_normal (h := eloop), exec_ret]
    simp [h12n]
  show run env sl (F + 4) "strlen" [p] mem sp = _
  unfold run
  rw [hlk]
  simp only [List.length_cons, List.length_nil, hfe, hbody]
  rfl

end LowIR.SSA
