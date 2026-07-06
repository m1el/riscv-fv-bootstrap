/-
  LowIR.ProgSim.ExecFacts — one-layer unfolder lemmas for `Prog.exec`
  (RESUME-PROGSIM Phase 0.2). Each peels EXACTLY one `fuel+1` layer of the
  clocked semantics into its sub-results, so downstream simulation proofs never
  need `simp [exec]` with an induction hypothesis in scope (the 128 GB OOM trap
  — see the gotcha memories). Ported from the Ctrl set
  (`CtrlStrtoullProof.lean`), retargeted at the D7/D8 `exec` (extra `dbase`/`pad`
  parameters, the real named `call`, and `ld`/`sd`/`cref`/`clen`).

  These live in `namespace LowIR.Prog` (like the Ctrl unfolders live in
  `LowIR.Ctrl`) so `exec`/`Stmt`/`St` resolve to the Prog versions directly.
-/
import LowIR.Prog

namespace LowIR.Prog

open LowIR (Cond evalCond)
open LowIR.Ctrl (Outcome)
open Rv64i (Word Byte)

variable (P : Program) (dbase : Name → Option Word) (pad : Name → Nat) (stackLo : Word)

/-! ### Leaf statements — pure value/outcome equations. -/

theorem exec_skip (fuel : Nat) (s : St) :
    exec P dbase pad stackLo (fuel+1) .skip s = some (s, .normal) := by simp [exec]

theorem exec_annot (fuel : Nat) (a : String) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.annot a) s = some (s, .normal) := by simp [exec]

theorem exec_addi (fuel rd rs : Nat) (imm : BitVec 12) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.addi rd rs imm) s
      = some (s.rset rd (s.rget rs + imm.signExtend 64), .normal) := by simp [exec]

theorem exec_add (fuel rd r1 r2 : Nat) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.add rd r1 r2) s
      = some (s.rset rd (s.rget r1 + s.rget r2), .normal) := by simp [exec]

theorem exec_sub (fuel rd r1 r2 : Nat) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.sub rd r1 r2) s
      = some (s.rset rd (s.rget r1 - s.rget r2), .normal) := by simp [exec]

theorem exec_orr (fuel rd r1 r2 : Nat) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.orr rd r1 r2) s
      = some (s.rset rd (s.rget r1 ||| s.rget r2), .normal) := by simp [exec]

theorem exec_slli (fuel rd rs sh : Nat) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.slli rd rs sh) s
      = some (s.rset rd (s.rget rs <<< sh), .normal) := by simp [exec]

theorem exec_srli (fuel rd rs sh : Nat) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.srli rd rs sh) s
      = some (s.rset rd (s.rget rs >>> sh), .normal) := by simp [exec]

theorem exec_lbu (fuel rd rs : Nat) (imm : BitVec 12) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.lbu rd rs imm) s
      = some (s.rset rd ((s.loadByte (s.rget rs + imm.signExtend 64)).setWidth 64), .normal) := by
  simp [exec]

theorem exec_sb (fuel rb rv : Nat) (imm : BitVec 12) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.sb rb rv imm) s
      = some (s.storeByte (s.rget rb + imm.signExtend 64) ((s.rget rv).setWidth 8), .normal) := by
  simp [exec]

theorem exec_ld (fuel rd rs : Nat) (imm : BitVec 12) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.ld rd rs imm) s
      = some (s.rset rd (s.loadWord (s.rget rs + imm.signExtend 64)), .normal) := by simp [exec]

theorem exec_sd (fuel rb rv : Nat) (imm : BitVec 12) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.sd rb rv imm) s
      = some (s.storeWord (s.rget rb + imm.signExtend 64) (s.rget rv), .normal) := by simp [exec]

theorem exec_brkB (fuel k : Nat) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.brkB k) s = some (s, .brk k) := by simp [exec]

theorem exec_contL (fuel k : Nat) (s : St) :
    exec P dbase pad stackLo (fuel+1) (.contL k) s = some (s, .cont k) := by simp [exec]

theorem exec_ret (fuel : Nat) (s : St) :
    exec P dbase pad stackLo (fuel+1) .ret s = some (s, .ret) := by simp [exec]

/-! ### Const-data references — conditioned on the address/length lookups. -/

theorem exec_cref (fuel rd : Nat) (d : Name) (s : St) {a : Word} (h : dbase d = some a) :
    exec P dbase pad stackLo (fuel+1) (.cref rd d) s = some (s.rset rd a, .normal) := by
  simp [exec, h]

theorem exec_clen (fuel rd : Nat) (d : Name) (s : St) {bs : List Byte}
    (h : List.lookup d P.data = some bs) :
    exec P dbase pad stackLo (fuel+1) (.clen rd d) s
      = some (s.rset rd (BitVec.ofNat 64 bs.length), .normal) := by
  simp [exec, h]

theorem exec_clen_none (fuel rd : Nat) (d : Name) (s : St)
    (h : List.lookup d P.data = none) :
    exec P dbase pad stackLo (fuel+1) (.clen rd d) s = none := by
  simp [exec, h]

theorem exec_cref_none (fuel rd : Nat) (d : Name) (s : St) (h : dbase d = none) :
    exec P dbase pad stackLo (fuel+1) (.cref rd d) s = none := by
  simp [exec, h]

/-! ### `ife` — collapse to the taken branch. -/

theorem exec_ife_then (fuel : Nat) (c : Cond) (a b : Reg) (t e : Stmt) (s : St)
    (h : evalCond c (s.rget a) (s.rget b) = true) :
    exec P dbase pad stackLo (fuel+1) (.ife c a b t e) s = exec P dbase pad stackLo fuel t s := by
  simp [exec, h]

theorem exec_ife_else (fuel : Nat) (c : Cond) (a b : Reg) (t e : Stmt) (s : St)
    (h : evalCond c (s.rget a) (s.rget b) = false) :
    exec P dbase pad stackLo (fuel+1) (.ife c a b t e) s = exec P dbase pad stackLo fuel e s := by
  simp [exec, h]

/-! ### `seq` — threads on `normal`, short-circuits otherwise. -/

theorem exec_seq_normal (fuel : Nat) (a b : Stmt) (s s' : St)
    (h : exec P dbase pad stackLo fuel a s = some (s', .normal)) :
    exec P dbase pad stackLo (fuel+1) (.seq a b) s = exec P dbase pad stackLo fuel b s' := by
  simp [exec, h]

theorem exec_seq_brk (fuel : Nat) (a b : Stmt) (s s' : St) (k : Nat)
    (h : exec P dbase pad stackLo fuel a s = some (s', .brk k)) :
    exec P dbase pad stackLo (fuel+1) (.seq a b) s = some (s', .brk k) := by simp [exec, h]

theorem exec_seq_cont (fuel : Nat) (a b : Stmt) (s s' : St) (k : Nat)
    (h : exec P dbase pad stackLo fuel a s = some (s', .cont k)) :
    exec P dbase pad stackLo (fuel+1) (.seq a b) s = some (s', .cont k) := by simp [exec, h]

theorem exec_seq_ret (fuel : Nat) (a b : Stmt) (s s' : St)
    (h : exec P dbase pad stackLo fuel a s = some (s', .ret)) :
    exec P dbase pad stackLo (fuel+1) (.seq a b) s = some (s', .ret) := by simp [exec, h]

theorem exec_seq_none (fuel : Nat) (a b : Stmt) (s : St)
    (h : exec P dbase pad stackLo fuel a s = none) :
    exec P dbase pad stackLo (fuel+1) (.seq a b) s = none := by simp [exec, h]

/-! ### `block` — the break-scope: catch `brk 0`, decrement deeper breaks. -/

theorem exec_block_normal (fuel : Nat) (body : Stmt) (s s' : St)
    (h : exec P dbase pad stackLo fuel body s = some (s', .normal)) :
    exec P dbase pad stackLo (fuel+1) (.block body) s = some (s', .normal) := by simp [exec, h]

theorem exec_block_catch (fuel : Nat) (body : Stmt) (s s' : St)
    (h : exec P dbase pad stackLo fuel body s = some (s', .brk 0)) :
    exec P dbase pad stackLo (fuel+1) (.block body) s = some (s', .normal) := by simp [exec, h]

theorem exec_block_brkS (fuel : Nat) (body : Stmt) (s s' : St) (k : Nat)
    (h : exec P dbase pad stackLo fuel body s = some (s', .brk (k+1))) :
    exec P dbase pad stackLo (fuel+1) (.block body) s = some (s', .brk k) := by simp [exec, h]

theorem exec_block_cont (fuel : Nat) (body : Stmt) (s s' : St) (k : Nat)
    (h : exec P dbase pad stackLo fuel body s = some (s', .cont k)) :
    exec P dbase pad stackLo (fuel+1) (.block body) s = some (s', .cont k) := by simp [exec, h]

theorem exec_block_ret (fuel : Nat) (body : Stmt) (s s' : St)
    (h : exec P dbase pad stackLo fuel body s = some (s', .ret)) :
    exec P dbase pad stackLo (fuel+1) (.block body) s = some (s', .ret) := by simp [exec, h]

theorem exec_block_none (fuel : Nat) (body : Stmt) (s : St)
    (h : exec P dbase pad stackLo fuel body s = none) :
    exec P dbase pad stackLo (fuel+1) (.block body) s = none := by simp [exec, h]

/-! ### `while` — the continue-scope + back-edge. -/

theorem exec_while_false (fuel : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s : St)
    (hc : evalCond c (s.rget a) (s.rget b) = false) :
    exec P dbase pad stackLo (fuel+1) (.while c a b body) s = some (s, .normal) := by simp [exec, hc]

theorem exec_while_normal (fuel : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s s' : St)
    (hc : evalCond c (s.rget a) (s.rget b) = true)
    (hb : exec P dbase pad stackLo fuel body s = some (s', .normal)) :
    exec P dbase pad stackLo (fuel+1) (.while c a b body) s
      = exec P dbase pad stackLo fuel (.while c a b body) s' := by simp [exec, hc, hb]

theorem exec_while_cont0 (fuel : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s s' : St)
    (hc : evalCond c (s.rget a) (s.rget b) = true)
    (hb : exec P dbase pad stackLo fuel body s = some (s', .cont 0)) :
    exec P dbase pad stackLo (fuel+1) (.while c a b body) s
      = exec P dbase pad stackLo fuel (.while c a b body) s' := by simp [exec, hc, hb]

theorem exec_while_contS (fuel : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s s' : St) (k : Nat)
    (hc : evalCond c (s.rget a) (s.rget b) = true)
    (hb : exec P dbase pad stackLo fuel body s = some (s', .cont (k+1))) :
    exec P dbase pad stackLo (fuel+1) (.while c a b body) s = some (s', .cont k) := by
  simp [exec, hc, hb]

theorem exec_while_brk (fuel : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s s' : St) (k : Nat)
    (hc : evalCond c (s.rget a) (s.rget b) = true)
    (hb : exec P dbase pad stackLo fuel body s = some (s', .brk k)) :
    exec P dbase pad stackLo (fuel+1) (.while c a b body) s = some (s', .brk k) := by
  simp [exec, hc, hb]

theorem exec_while_ret (fuel : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s s' : St)
    (hc : evalCond c (s.rget a) (s.rget b) = true)
    (hb : exec P dbase pad stackLo fuel body s = some (s', .ret)) :
    exec P dbase pad stackLo (fuel+1) (.while c a b body) s = some (s', .ret) := by
  simp [exec, hc, hb]

theorem exec_while_none (fuel : Nat) (c : Cond) (a b : Reg) (body : Stmt) (s : St)
    (hc : evalCond c (s.rget a) (s.rget b) = true)
    (hb : exec P dbase pad stackLo fuel body s = none) :
    exec P dbase pad stackLo (fuel+1) (.while c a b body) s = none := by simp [exec, hc, hb]

/-! ### `call` — the D7 activation. The successful case (callee falls off the
    end or `ret`s) returns to the caller with only `rets` copied back and the
    callee's memory kept. -/

theorem exec_call_ok (fuel argc rvc : Nat) (f : Name) (args : Vector Reg argc)
    (rets : Vector Reg rvc) (s s1 callee : St) (fd : FunDef) (o : Outcome)
    (hlk : List.lookup f P.env = some fd)
    (harity : (fd.argc == argc && fd.rvc == rvc) = true)
    (hfe : frameEnter stackLo fd (pad f) (args.toList.map s.rget) s.mem s.sp = some callee)
    (hbody : exec P dbase pad stackLo fuel fd.body callee = some (s1, o))
    (ho : o = .normal ∨ o = .ret) :
    exec P dbase pad stackLo (fuel+1) (.call argc rvc f args rets) s
      = some ((rets.toList.zip (fd.rets.toList.map s1.rget)).foldl
                (fun st rv => st.rset rv.1 rv.2) { s with mem := s1.mem }, .normal) := by
  rcases ho with rfl | rfl <;> simp [exec, hlk, harity, hfe, hbody]

theorem exec_call_lookup_none (fuel argc rvc : Nat) (f : Name) (args : Vector Reg argc)
    (rets : Vector Reg rvc) (s : St) (hlk : List.lookup f P.env = none) :
    exec P dbase pad stackLo (fuel+1) (.call argc rvc f args rets) s = none := by simp [exec, hlk]

/-- **Inversion for the successful call** — the shape the `lower_sim_cf` call case
    consumes. From a successful `.call` run, recover the callee (`lookup` + arity),
    its entry state (`frameEnter`), the body run and its live outcome
    (`.normal`/`.ret` — escaping brk/cont and overflow/lookup failures all force
    `h` to `none`), the caller-side return-register writeback, and `oc = .normal`. -/
theorem exec_call_inv (fuel argc rvc : Nat) (f : Name) (args : Vector Reg argc)
    (rets : Vector Reg rvc) (s s' : St) (oc : Outcome)
    (h : exec P dbase pad stackLo (fuel+1) (.call argc rvc f args rets) s = some (s', oc)) :
    ∃ (fd : FunDef) (callee s1 : St) (ocb : Outcome),
      List.lookup f P.env = some fd
      ∧ (fd.argc == argc && fd.rvc == rvc) = true
      ∧ frameEnter stackLo fd (pad f) (args.toList.map s.rget) s.mem s.sp = some callee
      ∧ exec P dbase pad stackLo fuel fd.body callee = some (s1, ocb)
      ∧ (ocb = Outcome.normal ∨ ocb = Outcome.ret)
      ∧ s' = (rets.toList.zip (fd.rets.toList.map s1.rget)).foldl
                (fun st rv => st.rset rv.1 rv.2) { s with mem := s1.mem }
      ∧ oc = Outcome.normal := by
  simp only [exec] at h
  split at h
  · simp at h
  · next fd hlk =>
    split at h
    · next harity =>
      split at h
      · next hfe => simp at h
      · next callee hfe =>
        split at h
        · next s1 hbody =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨fd, callee, s1, .normal, hlk, harity, hfe, hbody, Or.inl rfl, h.1.symm, h.2.symm⟩
        · next s1 hbody =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          exact ⟨fd, callee, s1, .ret, hlk, harity, hfe, hbody, Or.inr rfl, h.1.symm, h.2.symm⟩
        · simp at h
        · simp at h
    · next harity => simp at h

/-- Inversion of the top-level `run`: a successful run looks up `f`, enters its
    frame, and its body returns `normal`/`ret`. The `prog_sim` IL-side foundation
    (the entry into `entry` that the machine's stub `jal` + prologue mirror). -/
theorem run_inv {P : Program} {stackLo : Word} {fuel : Nat} {f : Name}
    {args : List Word} {mem : Word → Byte} {sp0 : Word} {pad : Name → Nat}
    {dataBase : Word} {s' : St}
    (h : run P stackLo fuel f args mem sp0 pad dataBase = some s') :
    ∃ (fd : FunDef) (st0 : St) (oc : Outcome),
      List.lookup f P.env = some fd
      ∧ frameEnter stackLo fd (pad f) args (installData dataBase P.data mem) sp0 = some st0
      ∧ exec P (dbaseOf dataBase P.data) pad stackLo fuel fd.body st0 = some (s', oc)
      ∧ (oc = Outcome.normal ∨ oc = Outcome.ret) := by
  simp only [run] at h
  split at h
  · simp at h
  · next fd hlk =>
    split at h
    · simp at h
    · next st0 hfe =>
      split at h
      · next s1 hbody =>
        simp only [Option.some.injEq] at h
        exact ⟨fd, st0, .normal, hlk, hfe, h ▸ hbody, Or.inl rfl⟩
      · next s1 hbody =>
        simp only [Option.some.injEq] at h
        exact ⟨fd, st0, .ret, hlk, hfe, h ▸ hbody, Or.inr rfl⟩
      · simp at h

end LowIR.Prog
