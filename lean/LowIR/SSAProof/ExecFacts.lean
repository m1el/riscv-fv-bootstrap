/-
  LowIR.SSAProof.ExecFacts — Phase 0 toolbox for the SSA hex0 proof
  (docs/RESUME-SSA-HEX0.md §Phase 0). One-layer unfolder lemmas for
  `LowIR.SSA.exec` (the clocked, valued-outcome semantics), the monotonicity
  facts `exec_mono`/`exec_mono_le`, the syntactic frame theorem `exec_frame`
  (P2 — replaces Ctrl's `Regs`/`Pres` bookkeeping), and a bare-memory
  restatement of the borrow separation layer (P3).

  Modelled on `LowIR.ProgSim.ExecFacts` / `LowIR.Ctrl`'s unfolder set, but the
  SSA `exec` has valued outcomes, `catch0` for the `block`/`ife` break-scopes,
  and block-parameter `while` (the back-edge re-executes a *rebuilt* while at
  the same fuel). Everything lives in `namespace LowIR.SSA` so `exec`/`Stmt`/
  `St`/`Outcome` resolve to the SSA versions directly.
-/
import LowIR.SSA

namespace LowIR.SSA

open LowIR (Cond evalCond)
open Rv64i (Word Byte)

variable (env : Env) (stackLo : Word)

/-! ### Operand / bind-outs computation rules -/

@[simp] theorem evalOpnd_reg (s : St) (r : Reg) : evalOpnd s (.reg r) = s.rget r := rfl
@[simp] theorem evalOpnd_const (s : St) (v : Word) : evalOpnd s (.const v) = v := rfl

@[simp] theorem bindOuts_nil (s : St) (vs : List Word) : bindOuts s [] vs = s := rfl
@[simp] theorem bindOuts_nil_vs (s : St) (outs : List Reg) : bindOuts s outs [] = s := by
  simp [bindOuts]
@[simp] theorem bindOuts_cons (s : St) (o : Reg) (os : List Reg) (v : Word) (vs : List Word) :
    bindOuts s (o :: os) (v :: vs) = bindOuts (s.rset o v) os vs := rfl

/-! ### Leaf statements — pure value/outcome equations. -/

theorem exec_skip (fuel : Nat) (s : St) :
    exec env stackLo (fuel+1) .skip s = some (s, .normal) := by simp [exec]

theorem exec_annot (fuel : Nat) (a : String) (s : St) :
    exec env stackLo (fuel+1) (.annot a) s = some (s, .normal) := by simp [exec]

theorem exec_addi (fuel rd rs : Nat) (imm : BitVec 12) (s : St) :
    exec env stackLo (fuel+1) (.addi rd rs imm) s
      = some (s.rset rd (s.rget rs + imm.signExtend 64), .normal) := by simp [exec]

theorem exec_add (fuel rd r1 r2 : Nat) (s : St) :
    exec env stackLo (fuel+1) (.add rd r1 r2) s
      = some (s.rset rd (s.rget r1 + s.rget r2), .normal) := by simp [exec]

theorem exec_sub (fuel rd r1 r2 : Nat) (s : St) :
    exec env stackLo (fuel+1) (.sub rd r1 r2) s
      = some (s.rset rd (s.rget r1 - s.rget r2), .normal) := by simp [exec]

theorem exec_orr (fuel rd r1 r2 : Nat) (s : St) :
    exec env stackLo (fuel+1) (.orr rd r1 r2) s
      = some (s.rset rd (s.rget r1 ||| s.rget r2), .normal) := by simp [exec]

theorem exec_slli (fuel rd rs sh : Nat) (s : St) :
    exec env stackLo (fuel+1) (.slli rd rs sh) s
      = some (s.rset rd (s.rget rs <<< sh), .normal) := by simp [exec]

theorem exec_srli (fuel rd rs sh : Nat) (s : St) :
    exec env stackLo (fuel+1) (.srli rd rs sh) s
      = some (s.rset rd (s.rget rs >>> sh), .normal) := by simp [exec]

theorem exec_lbu (fuel rd rs : Nat) (imm : BitVec 12) (s : St) :
    exec env stackLo (fuel+1) (.lbu rd rs imm) s
      = some (s.rset rd ((s.loadByte (s.rget rs + imm.signExtend 64)).setWidth 64), .normal) := by
  simp [exec]

theorem exec_sb (fuel rb rv : Nat) (imm : BitVec 12) (s : St) :
    exec env stackLo (fuel+1) (.sb rb rv imm) s
      = some (s.storeByte (s.rget rb + imm.signExtend 64) ((s.rget rv).setWidth 8), .normal) := by
  simp [exec]

theorem exec_ld (fuel rd rs : Nat) (imm : BitVec 12) (s : St) :
    exec env stackLo (fuel+1) (.ld rd rs imm) s
      = some (s.rset rd (s.loadWord (s.rget rs + imm.signExtend 64)), .normal) := by simp [exec]

theorem exec_sd (fuel rb rv : Nat) (imm : BitVec 12) (s : St) :
    exec env stackLo (fuel+1) (.sd rb rv imm) s
      = some (s.storeWord (s.rget rb + imm.signExtend 64) (s.rget rv), .normal) := by simp [exec]

theorem exec_brk (fuel k : Nat) (vs : List Opnd) (s : St) :
    exec env stackLo (fuel+1) (.brk k vs) s = some (s, .brk k (vs.map (evalOpnd s))) := by simp [exec]

theorem exec_cont (fuel k : Nat) (vs : List Opnd) (s : St) :
    exec env stackLo (fuel+1) (.cont k vs) s = some (s, .cont k (vs.map (evalOpnd s))) := by simp [exec]

theorem exec_ret (fuel : Nat) (vs : List Opnd) (s : St) :
    exec env stackLo (fuel+1) (.ret vs) s = some (s, .ret (vs.map (evalOpnd s))) := by simp [exec]

/-! ### `seq` — threads on `normal`, short-circuits otherwise. -/

theorem exec_seq_normal (fuel : Nat) (a b : Stmt) (s s' : St)
    (h : exec env stackLo fuel a s = some (s', .normal)) :
    exec env stackLo (fuel+1) (.seq a b) s = exec env stackLo fuel b s' := by simp [exec, h]

theorem exec_seq_brk (fuel : Nat) (a b : Stmt) (s s' : St) (k : Nat) (vs : List Word)
    (h : exec env stackLo fuel a s = some (s', .brk k vs)) :
    exec env stackLo (fuel+1) (.seq a b) s = some (s', .brk k vs) := by simp [exec, h]

theorem exec_seq_cont (fuel : Nat) (a b : Stmt) (s s' : St) (k : Nat) (vs : List Word)
    (h : exec env stackLo fuel a s = some (s', .cont k vs)) :
    exec env stackLo (fuel+1) (.seq a b) s = some (s', .cont k vs) := by simp [exec, h]

theorem exec_seq_ret (fuel : Nat) (a b : Stmt) (s s' : St) (vs : List Word)
    (h : exec env stackLo fuel a s = some (s', .ret vs)) :
    exec env stackLo (fuel+1) (.seq a b) s = some (s', .ret vs) := by simp [exec, h]

theorem exec_seq_none (fuel : Nat) (a b : Stmt) (s : St)
    (h : exec env stackLo fuel a s = none) :
    exec env stackLo (fuel+1) (.seq a b) s = none := by simp [exec, h]

/-! ### `catch0` — the value-binding break-scope shared by `block`/`ife`. -/

theorem catch0_none (outs : List Reg) : catch0 outs none = none := rfl

theorem catch0_brk0 (outs : List Reg) (s : St) (vs : List Word) (h : vs.length = outs.length) :
    catch0 outs (some (s, .brk 0 vs)) = some (bindOuts s outs vs, .normal) := by
  simp only [catch0]; rw [if_pos]; rw [h]; exact (beq_self_eq_true _)

theorem catch0_brkS (outs : List Reg) (s : St) (k : Nat) (vs : List Word) :
    catch0 outs (some (s, .brk (k+1) vs)) = some (s, .brk k vs) := rfl

theorem catch0_cont (outs : List Reg) (s : St) (k : Nat) (vs : List Word) :
    catch0 outs (some (s, .cont k vs)) = some (s, .cont k vs) := rfl

theorem catch0_ret (outs : List Reg) (s : St) (vs : List Word) :
    catch0 outs (some (s, .ret vs)) = some (s, .ret vs) := rfl

theorem catch0_nil_normal (s : St) : catch0 [] (some (s, .normal)) = some (s, .normal) := rfl

/-! ### `block` and `ife` — reduce to `catch0` of the body / selected arm. -/

theorem exec_block (fuel : Nat) (outs : List Reg) (body : Stmt) (s : St) :
    exec env stackLo (fuel+1) (.block outs body) s
      = catch0 outs (exec env stackLo fuel body s) := by simp [exec]

theorem exec_ife_then (fuel : Nat) (c : Cond) (ca cb : Reg) (outs : List Reg) (t e : Stmt) (s : St)
    (hc : evalCond c (s.rget ca) (s.rget cb) = true) :
    exec env stackLo (fuel+1) (.ife c ca cb outs t e) s
      = catch0 outs (exec env stackLo fuel t s) := by simp [exec, hc]

theorem exec_ife_else (fuel : Nat) (c : Cond) (ca cb : Reg) (outs : List Reg) (t e : Stmt) (s : St)
    (hc : evalCond c (s.rget ca) (s.rget cb) = false) :
    exec env stackLo (fuel+1) (.ife c ca cb outs t e) s
      = catch0 outs (exec env stackLo fuel e s) := by simp [exec, hc]

/-! ### `while` — block-parameter loop. `exec_while_unfold` peels one head
    entry (the length check + guard + arg binding) into the post-branch match;
    the resolved lemmas below fix a branch outcome. `s0` is the arg-bound
    entry state, `branch` the guard-selected body/dflt. -/

theorem exec_while_unfold (fuel : Nat) (outs : List Reg) (inits : List Opnd) (args : List Reg)
    (c : Cond) (ca cb : Reg) (body dflt : Stmt) (s : St)
    (hlen : inits.length = args.length) :
    exec env stackLo (fuel+1) (.«while» outs inits args c ca cb body dflt) s
      = (match exec env stackLo fuel
             (if evalCond c ((bindOuts s args (inits.map (evalOpnd s))).rget ca)
                            ((bindOuts s args (inits.map (evalOpnd s))).rget cb) then body else dflt)
             (bindOuts s args (inits.map (evalOpnd s))) with
         | some (s1, .cont 0 vs) =>
             if vs.length == args.length then
               exec env stackLo fuel (.«while» outs (vs.map .const) args c ca cb body dflt) s1
             else none
         | some (s1, .brk 0 vs)  =>
             if vs.length == outs.length then some (bindOuts s1 outs vs, .normal) else none
         | some (s1, .brk (k+1) vs)  => some (s1, .brk k vs)
         | some (s1, .cont (k+1) vs) => some (s1, .cont k vs)
         | some (s1, .ret vs)        => some (s1, .ret vs)
         | some (_, .normal)         => none
         | none                      => none) := by
  simp only [exec]
  rw [if_pos (by rw [hlen]; exact beq_self_eq_true _)]
  rfl

/-- Guard-true, body continues the loop (`cont 0`): re-execute the rebuilt while. -/
theorem exec_while_cont0 (fuel : Nat) (outs : List Reg) (inits : List Opnd) (args : List Reg)
    (c : Cond) (ca cb : Reg) (body dflt : Stmt) (s s1 : St) (vs : List Word) (s0 : St)
    (hlen : inits.length = args.length)
    (hs0 : s0 = bindOuts s args (inits.map (evalOpnd s)))
    (hc : evalCond c (s0.rget ca) (s0.rget cb) = true)
    (hb : exec env stackLo fuel body s0 = some (s1, .cont 0 vs))
    (hvs : vs.length = args.length) :
    exec env stackLo (fuel+1) (.«while» outs inits args c ca cb body dflt) s
      = exec env stackLo fuel (.«while» outs (vs.map .const) args c ca cb body dflt) s1 := by
  rw [exec_while_unfold (hlen := hlen)]
  simp only [← hs0, hc, if_true, hb]
  rw [if_pos (by rw [hvs]; exact beq_self_eq_true _)]

/-- Guard-true, body escapes one level up (`cont (k+1)`): shift to `cont k`. -/
theorem exec_while_contS (fuel : Nat) (outs : List Reg) (inits : List Opnd) (args : List Reg)
    (c : Cond) (ca cb : Reg) (body dflt : Stmt) (s s1 : St) (k : Nat) (vs : List Word) (s0 : St)
    (hlen : inits.length = args.length)
    (hs0 : s0 = bindOuts s args (inits.map (evalOpnd s)))
    (hc : evalCond c (s0.rget ca) (s0.rget cb) = true)
    (hb : exec env stackLo fuel body s0 = some (s1, .cont (k+1) vs)) :
    exec env stackLo (fuel+1) (.«while» outs inits args c ca cb body dflt) s
      = some (s1, .cont k vs) := by
  rw [exec_while_unfold (hlen := hlen)]; simp only [← hs0, hc, if_true, hb]

/-- Guard-true, body breaks out (`brk 0`): bind outs, normalize. -/
theorem exec_while_brk0 (fuel : Nat) (outs : List Reg) (inits : List Opnd) (args : List Reg)
    (c : Cond) (ca cb : Reg) (body dflt : Stmt) (s s1 : St) (vs : List Word) (s0 : St)
    (hlen : inits.length = args.length)
    (hs0 : s0 = bindOuts s args (inits.map (evalOpnd s)))
    (hc : evalCond c (s0.rget ca) (s0.rget cb) = true)
    (hb : exec env stackLo fuel body s0 = some (s1, .brk 0 vs))
    (hvs : vs.length = outs.length) :
    exec env stackLo (fuel+1) (.«while» outs inits args c ca cb body dflt) s
      = some (bindOuts s1 outs vs, .normal) := by
  rw [exec_while_unfold (hlen := hlen)]
  simp only [← hs0, hc, if_true, hb]
  rw [if_pos (by rw [hvs]; exact beq_self_eq_true _)]

/-- Guard-true, body breaks further out (`brk (k+1)`): shift to `brk k`. -/
theorem exec_while_brkS (fuel : Nat) (outs : List Reg) (inits : List Opnd) (args : List Reg)
    (c : Cond) (ca cb : Reg) (body dflt : Stmt) (s s1 : St) (k : Nat) (vs : List Word) (s0 : St)
    (hlen : inits.length = args.length)
    (hs0 : s0 = bindOuts s args (inits.map (evalOpnd s)))
    (hc : evalCond c (s0.rget ca) (s0.rget cb) = true)
    (hb : exec env stackLo fuel body s0 = some (s1, .brk (k+1) vs)) :
    exec env stackLo (fuel+1) (.«while» outs inits args c ca cb body dflt) s
      = some (s1, .brk k vs) := by
  rw [exec_while_unfold (hlen := hlen)]; simp only [← hs0, hc, if_true, hb]

/-- Guard-true, body returns from the function (`ret`): pass it out. -/
theorem exec_while_ret (fuel : Nat) (outs : List Reg) (inits : List Opnd) (args : List Reg)
    (c : Cond) (ca cb : Reg) (body dflt : Stmt) (s s1 : St) (vs : List Word) (s0 : St)
    (hlen : inits.length = args.length)
    (hs0 : s0 = bindOuts s args (inits.map (evalOpnd s)))
    (hc : evalCond c (s0.rget ca) (s0.rget cb) = true)
    (hb : exec env stackLo fuel body s0 = some (s1, .ret vs)) :
    exec env stackLo (fuel+1) (.«while» outs inits args c ca cb body dflt) s
      = some (s1, .ret vs) := by
  rw [exec_while_unfold (hlen := hlen)]; simp only [← hs0, hc, if_true, hb]

/-! Guard-FALSE (branch = `dflt`) counterparts — only the outcomes the ports use. -/

/-- Guard-false, dflt breaks out with the loop-carried outs (`brk 0`). -/
theorem exec_while_F_brk0 (fuel : Nat) (outs : List Reg) (inits : List Opnd) (args : List Reg)
    (c : Cond) (ca cb : Reg) (body dflt : Stmt) (s s1 : St) (vs : List Word) (s0 : St)
    (hlen : inits.length = args.length)
    (hs0 : s0 = bindOuts s args (inits.map (evalOpnd s)))
    (hc : evalCond c (s0.rget ca) (s0.rget cb) = false)
    (hb : exec env stackLo fuel dflt s0 = some (s1, .brk 0 vs))
    (hvs : vs.length = outs.length) :
    exec env stackLo (fuel+1) (.«while» outs inits args c ca cb body dflt) s
      = some (bindOuts s1 outs vs, .normal) := by
  rw [exec_while_unfold (hlen := hlen)]
  simp only [← hs0]
  rw [if_neg (show ¬ (evalCond c (s0.rget ca) (s0.rget cb) = true) by rw [hc]; decide)]
  simp only [hb]
  rw [if_pos (by rw [hvs]; exact beq_self_eq_true _)]

/-- Guard-false, dflt returns from the function (`ret`) — hex0's success exit. -/
theorem exec_while_F_ret (fuel : Nat) (outs : List Reg) (inits : List Opnd) (args : List Reg)
    (c : Cond) (ca cb : Reg) (body dflt : Stmt) (s s1 : St) (vs : List Word) (s0 : St)
    (hlen : inits.length = args.length)
    (hs0 : s0 = bindOuts s args (inits.map (evalOpnd s)))
    (hc : evalCond c (s0.rget ca) (s0.rget cb) = false)
    (hb : exec env stackLo fuel dflt s0 = some (s1, .ret vs)) :
    exec env stackLo (fuel+1) (.«while» outs inits args c ca cb body dflt) s
      = some (s1, .ret vs) := by
  rw [exec_while_unfold (hlen := hlen)]
  simp only [← hs0]
  rw [if_neg (show ¬ (evalCond c (s0.rget ca) (s0.rget cb) = true) by rw [hc]; decide)]
  simp only [hb]

/-- Guard-false, dflt continues further out (`cont (k+1)`) — skipComment's dflt. -/
theorem exec_while_F_contS (fuel : Nat) (outs : List Reg) (inits : List Opnd) (args : List Reg)
    (c : Cond) (ca cb : Reg) (body dflt : Stmt) (s s1 : St) (k : Nat) (vs : List Word) (s0 : St)
    (hlen : inits.length = args.length)
    (hs0 : s0 = bindOuts s args (inits.map (evalOpnd s)))
    (hc : evalCond c (s0.rget ca) (s0.rget cb) = false)
    (hb : exec env stackLo fuel dflt s0 = some (s1, .cont (k+1) vs)) :
    exec env stackLo (fuel+1) (.«while» outs inits args c ca cb body dflt) s
      = some (s1, .cont k vs) := by
  rw [exec_while_unfold (hlen := hlen)]
  simp only [← hs0]
  rw [if_neg (show ¬ (evalCond c (s0.rget ca) (s0.rget cb) = true) by rw [hc]; decide)]
  simp only [hb]

/-- Length mismatch on the loop args: `exec` is `none` regardless of fuel. -/
theorem exec_while_badlen (fuel : Nat) (outs : List Reg) (inits : List Opnd) (args : List Reg)
    (c : Cond) (ca cb : Reg) (body dflt : Stmt) (s : St)
    (hlen : ¬ inits.length = args.length) :
    exec env stackLo (fuel+1) (.«while» outs inits args c ca cb body dflt) s = none := by
  simp only [exec]
  rw [if_neg (by simpa using hlen)]

/-! ### `call` — activation record. `exec_call_body` exposes the callee body
    execution; the *-none lemmas cover the failure paths (used by `exec_mono`). -/

theorem exec_call_lookup_none (fuel : Nat) (f : Name) (argOps : List Opnd) (outs : List Reg) (s : St)
    (hlk : List.lookup f env = none) :
    exec env stackLo (fuel+1) (.call f argOps outs) s = none := by simp [exec, hlk]

theorem exec_call_arity_false (fuel : Nat) (f : Name) (argOps : List Opnd) (outs : List Reg)
    (s : St) (fd : FunDef) (hlk : List.lookup f env = some fd)
    (harity : (argOps.length == fd.params.length && outs.length == fd.rvc) = false) :
    exec env stackLo (fuel+1) (.call f argOps outs) s = none := by simp [exec, hlk, harity]

theorem exec_call_fe_none (fuel : Nat) (f : Name) (argOps : List Opnd) (outs : List Reg)
    (s : St) (fd : FunDef) (hlk : List.lookup f env = some fd)
    (harity : (argOps.length == fd.params.length && outs.length == fd.rvc) = true)
    (hfe : frameEnter stackLo fd (argOps.map (evalOpnd s)) s.mem s.sp = none) :
    exec env stackLo (fuel+1) (.call f argOps outs) s = none := by simp [exec, hlk, harity, hfe]

theorem exec_call_body (fuel : Nat) (f : Name) (argOps : List Opnd) (outs : List Reg)
    (s callee : St) (fd : FunDef) (hlk : List.lookup f env = some fd)
    (harity : (argOps.length == fd.params.length && outs.length == fd.rvc) = true)
    (hfe : frameEnter stackLo fd (argOps.map (evalOpnd s)) s.mem s.sp = some callee) :
    exec env stackLo (fuel+1) (.call f argOps outs) s
      = (match exec env stackLo fuel fd.body callee with
         | some (s1, .ret vs) =>
             if vs.length == fd.rvc then
               some (bindOuts { s with mem := s1.mem } outs vs, .normal) else none
         | some (s1, .normal) =>
             if fd.rvc == 0 then some ({ s with mem := s1.mem }, .normal) else none
         | some _ => none
         | none => none) := by
  simp only [exec, hlk, harity, hfe, if_true]
  rfl

/-! ### Register / bind-outs frame helpers (P2 support). -/

theorem rset_regs_ne (s : St) (i : Reg) (v : Word) (r : Reg) (h : r ≠ i) :
    (s.rset i v).regs r = s.regs r := by
  unfold Prog.St.rset
  split
  · rfl
  · show (if r = i then v else s.regs r) = s.regs r
    rw [if_neg h]

theorem bindOuts_regs_not_mem (outs : List Reg) : ∀ (vs : List Word) (s : St) (r : Reg),
    r ∉ outs → (bindOuts s outs vs).regs r = s.regs r := by
  induction outs with
  | nil => intro vs s r _; rfl
  | cons o os ih =>
    intro vs s r hr
    simp only [List.mem_cons, not_or] at hr
    obtain ⟨hne, hnotos⟩ := hr
    cases vs with
    | nil => rfl
    | cons v vs =>
      rw [bindOuts_cons, ih vs (s.rset o v) r hnotos, rset_regs_ne s o v r hne]

theorem storeByte_regs (s : St) (a : Word) (b : Byte) (r : Reg) :
    (s.storeByte a b).regs r = s.regs r := rfl

theorem storeWord_regs (s : St) (a v : Word) (r : Reg) :
    (s.storeWord a v).regs r = s.regs r := rfl

/-! ### `exec_mono` (P4) — more fuel never changes a `some` result. The
    guard-agnostic proof: unfold one head layer of the `while` (same branch
    expression at both fuels), bump the sub-execution with the IH, and only the
    `cont 0` back-edge recurses (also discharged by the IH on the rebuilt
    while). -/

theorem exec_mono (f : Nat) : ∀ (stmt : Stmt) (s : St) (r : St × Outcome),
    exec env stackLo f stmt s = some r → exec env stackLo (f+1) stmt s = some r := by
  induction f with
  | zero => intro stmt s r h; rw [show exec env stackLo 0 stmt s = none from rfl] at h; simp at h
  | succ f ih =>
    intro stmt s r h
    cases stmt with
    | skip => simpa only [exec] using h
    | annot => simpa only [exec] using h
    | addi => simpa only [exec] using h
    | add => simpa only [exec] using h
    | sub => simpa only [exec] using h
    | orr => simpa only [exec] using h
    | slli => simpa only [exec] using h
    | srli => simpa only [exec] using h
    | lbu => simpa only [exec] using h
    | sb => simpa only [exec] using h
    | ld => simpa only [exec] using h
    | sd => simpa only [exec] using h
    | brk => simpa only [exec] using h
    | cont => simpa only [exec] using h
    | ret => simpa only [exec] using h
    | seq a b =>
      cases ha : exec env stackLo f a s with
      | none => rw [exec_seq_none (h := ha)] at h; exact absurd h (by simp)
      | some r' =>
        obtain ⟨s', o⟩ := r'
        have ha1 := ih a s (s', o) ha
        cases o with
        | normal =>
          rw [exec_seq_normal (h := ha)] at h
          rw [exec_seq_normal (h := ha1)]; exact ih b s' r h
        | brk k vs =>
          rw [exec_seq_brk (h := ha)] at h; rw [exec_seq_brk (h := ha1)]; exact h
        | cont k vs =>
          rw [exec_seq_cont (h := ha)] at h; rw [exec_seq_cont (h := ha1)]; exact h
        | ret vs =>
          rw [exec_seq_ret (h := ha)] at h; rw [exec_seq_ret (h := ha1)]; exact h
    | block outs body =>
      rw [exec_block] at h ⊢
      cases hb : exec env stackLo f body s with
      | none => rw [hb] at h; simp only [catch0_none] at h; exact absurd h (by simp)
      | some r' =>
        obtain ⟨sb, ob⟩ := r'
        rw [hb] at h; rw [ih body s (sb, ob) hb]; exact h
    | ife c ca cb outs t e =>
      cases hcond : evalCond c (s.rget ca) (s.rget cb) with
      | true =>
        rw [exec_ife_then (hc := hcond)] at h; rw [exec_ife_then (hc := hcond)]
        cases ht : exec env stackLo f t s with
        | none => rw [ht] at h; simp only [catch0_none] at h; exact absurd h (by simp)
        | some r' => obtain ⟨st, ot⟩ := r'; rw [ht] at h; rw [ih t s (st, ot) ht]; exact h
      | false =>
        rw [exec_ife_else (hc := hcond)] at h; rw [exec_ife_else (hc := hcond)]
        cases he : exec env stackLo f e s with
        | none => rw [he] at h; simp only [catch0_none] at h; exact absurd h (by simp)
        | some r' => obtain ⟨se, oe⟩ := r'; rw [he] at h; rw [ih e s (se, oe) he]; exact h
    | «while» outs inits args c ca cb body dflt =>
      by_cases hlen : inits.length = args.length
      · rw [exec_while_unfold (hlen := hlen)] at h ⊢
        generalize hBdef : bindOuts s args (inits.map (evalOpnd s)) = B at h ⊢
        generalize hbrdef : (if evalCond c (B.rget ca) (B.rget cb) then body else dflt) = branch at h ⊢
        cases hbr : exec env stackLo f branch B with
        | none => rw [hbr] at h; exact absurd h (by simp)
        | some r' =>
          obtain ⟨s1, o1⟩ := r'
          have hb1 := ih branch B (s1, o1) hbr
          rw [hbr] at h; rw [hb1]
          cases o1 with
          | normal => exact absurd h (by simp)
          | ret vs => exact h
          | brk k vs =>
            cases k with
            | zero =>
              by_cases hvs : (vs.length == outs.length) = true
              · simp only [hvs, if_true] at h ⊢; exact h
              · simp only [Bool.not_eq_true] at hvs; simp only [hvs] at h; exact absurd h (by simp)
            | succ k => exact h
          | cont k vs =>
            cases k with
            | zero =>
              by_cases hvs : (vs.length == args.length) = true
              · simp only [hvs, if_true] at h ⊢
                exact ih (.«while» outs (vs.map .const) args c ca cb body dflt) s1 r h
              · simp only [Bool.not_eq_true] at hvs; simp only [hvs] at h; exact absurd h (by simp)
            | succ k => exact h
      · rw [exec_while_badlen (hlen := hlen)] at h; exact absurd h (by simp)
    | call f' argOps outs =>
      cases hlk : List.lookup f' env with
      | none => rw [exec_call_lookup_none (hlk := hlk)] at h; exact absurd h (by simp)
      | some fd =>
        by_cases harity : (argOps.length == fd.params.length && outs.length == fd.rvc) = true
        · cases hfe : frameEnter stackLo fd (argOps.map (evalOpnd s)) s.mem s.sp with
          | none =>
            rw [exec_call_fe_none (hlk := hlk) (harity := harity) (hfe := hfe)] at h; exact absurd h (by simp)
          | some callee =>
            rw [exec_call_body (hlk := hlk) (harity := harity) (hfe := hfe)] at h
            rw [exec_call_body (hlk := hlk) (harity := harity) (hfe := hfe)]
            cases hcb : exec env stackLo f fd.body callee with
            | none => rw [hcb] at h; exact absurd h (by simp)
            | some r' => obtain ⟨s1, o1⟩ := r'; rw [hcb] at h; rw [ih fd.body callee (s1, o1) hcb]; exact h
        · rw [exec_call_arity_false (hlk := hlk) (harity := Bool.not_eq_true _ ▸ harity)] at h
          exact absurd h (by simp)

theorem exec_mono_le {f f' : Nat} (hle : f ≤ f') {stmt : Stmt} {s : St} {r : St × Outcome}
    (he : exec env stackLo f stmt s = some r) : exec env stackLo f' stmt s = some r := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => exact he
  | succ k ih => rw [show f + (k+1) = (f+k)+1 from rfl]; exact exec_mono env stackLo (f+k) stmt s r ih

/-! ### `exec_frame` (P2) — the syntactic frame theorem. `exec` only ever
    writes registers textually in `defs stmt`; every `r ∉ defs stmt` is
    preserved. Replaces Ctrl's `Regs`/`Pres` bookkeeping with one metatheorem
    (no checker hypothesis). Structural fuel induction, one case per
    constructor; `catch0_frame` factors the break-scope outcome analysis. -/

/-- Frame for a `catch0` break-scope: for `r ∉ outs`, the caught state's regs
    agree with the arm's regs (`brk 0` binds only `outs`; every other outcome
    passes the arm state through). -/
theorem catch0_frame (outs : List Reg) (sx : St) (ox : Outcome) (s' : St) (oc : Outcome)
    (hc : catch0 outs (some (sx, ox)) = some (s', oc)) (r : Reg) (hr : r ∉ outs) :
    s'.regs r = sx.regs r := by
  cases ox with
  | normal =>
    cases outs with
    | nil => rw [catch0_nil_normal] at hc; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj hc); rfl
    | cons o os => simp [catch0] at hc
  | brk k vs =>
    cases k with
    | zero =>
      by_cases hvs : vs.length = outs.length
      · rw [catch0_brk0 _ _ _ hvs] at hc
        obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj hc)
        exact bindOuts_regs_not_mem outs vs sx r hr
      · simp only [catch0] at hc
        rw [if_neg (by simpa using hvs)] at hc
        exact absurd hc (by simp)
    | succ k => rw [catch0_brkS] at hc; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj hc); rfl
  | cont k vs => rw [catch0_cont] at hc; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj hc); rfl
  | ret vs => rw [catch0_ret] at hc; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj hc); rfl

theorem exec_frame (f : Nat) : ∀ (stmt : Stmt) (s s' : St) (oc : Outcome),
    exec env stackLo f stmt s = some (s', oc) → ∀ r, r ∉ defs stmt → s'.regs r = s.regs r := by
  induction f with
  | zero => intro stmt s s' oc h; rw [show exec env stackLo 0 stmt s = none from rfl] at h; simp at h
  | succ f ih =>
    intro stmt s s' oc h r hr
    cases stmt with
    | skip => rw [exec_skip] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); rfl
    | annot => rw [exec_annot] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); rfl
    | addi rd rs imm =>
      rw [exec_addi] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
      exact rset_regs_ne s rd _ r (by simpa [defs] using hr)
    | add rd r1 r2 =>
      rw [exec_add] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
      exact rset_regs_ne s rd _ r (by simpa [defs] using hr)
    | sub rd r1 r2 =>
      rw [exec_sub] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
      exact rset_regs_ne s rd _ r (by simpa [defs] using hr)
    | orr rd r1 r2 =>
      rw [exec_orr] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
      exact rset_regs_ne s rd _ r (by simpa [defs] using hr)
    | slli rd rs sh =>
      rw [exec_slli] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
      exact rset_regs_ne s rd _ r (by simpa [defs] using hr)
    | srli rd rs sh =>
      rw [exec_srli] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
      exact rset_regs_ne s rd _ r (by simpa [defs] using hr)
    | lbu rd rs imm =>
      rw [exec_lbu] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
      exact rset_regs_ne s rd _ r (by simpa [defs] using hr)
    | ld rd rs imm =>
      rw [exec_ld] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
      exact rset_regs_ne s rd _ r (by simpa [defs] using hr)
    | sb rb rv imm =>
      rw [exec_sb] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); exact storeByte_regs _ _ _ _
    | sd rb rv imm =>
      rw [exec_sd] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); exact storeWord_regs _ _ _ _
    | brk k vs => rw [exec_brk] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); rfl
    | cont k vs => rw [exec_cont] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); rfl
    | ret vs => rw [exec_ret] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); rfl
    | seq a b =>
      simp only [defs, List.mem_append, not_or] at hr
      obtain ⟨hra, hrb⟩ := hr
      cases ha : exec env stackLo f a s with
      | none => rw [exec_seq_none (h := ha)] at h; exact absurd h (by simp)
      | some r' =>
        obtain ⟨sa, oa⟩ := r'
        have hsa := ih a s sa oa ha r hra
        cases oa with
        | normal =>
          rw [exec_seq_normal (h := ha)] at h
          exact (ih b sa s' oc h r hrb).trans hsa
        | brk k vs =>
          rw [exec_seq_brk (h := ha)] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); exact hsa
        | cont k vs =>
          rw [exec_seq_cont (h := ha)] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); exact hsa
        | ret vs =>
          rw [exec_seq_ret (h := ha)] at h; obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); exact hsa
    | block outs body =>
      simp only [defs, List.mem_append, not_or] at hr
      obtain ⟨hro, hrb⟩ := hr
      rw [exec_block] at h
      cases hb : exec env stackLo f body s with
      | none => rw [hb, catch0_none] at h; exact absurd h (by simp)
      | some r' =>
        obtain ⟨sb, ob⟩ := r'
        rw [hb] at h
        exact (catch0_frame outs sb ob s' oc h r hro).trans (ih body s sb ob hb r hrb)
    | ife c ca cb outs t e =>
      simp only [defs, List.mem_append, not_or] at hr
      obtain ⟨⟨hro, hrt⟩, hre⟩ := hr
      cases hcond : evalCond c (s.rget ca) (s.rget cb) with
      | true =>
        rw [exec_ife_then (hc := hcond)] at h
        cases ht : exec env stackLo f t s with
        | none => rw [ht, catch0_none] at h; exact absurd h (by simp)
        | some r' =>
          obtain ⟨st, ot⟩ := r'; rw [ht] at h
          exact (catch0_frame outs st ot s' oc h r hro).trans (ih t s st ot ht r hrt)
      | false =>
        rw [exec_ife_else (hc := hcond)] at h
        cases he : exec env stackLo f e s with
        | none => rw [he, catch0_none] at h; exact absurd h (by simp)
        | some r' =>
          obtain ⟨se, oe⟩ := r'; rw [he] at h
          exact (catch0_frame outs se oe s' oc h r hro).trans (ih e s se oe he r hre)
    | «while» outs inits args c ca cb body dflt =>
      simp only [defs, List.mem_append, not_or] at hr
      obtain ⟨⟨⟨hro, hrargs⟩, hrbody⟩, hrdflt⟩ := hr
      by_cases hlen : inits.length = args.length
      · have hBr : (bindOuts s args (inits.map (evalOpnd s))).regs r = s.regs r :=
          bindOuts_regs_not_mem args _ s r hrargs
        have hbrdefs : r ∉ defs (if evalCond c ((bindOuts s args (inits.map (evalOpnd s))).rget ca)
                                      ((bindOuts s args (inits.map (evalOpnd s))).rget cb)
                                 then body else dflt) := by
          split
          · exact hrbody
          · exact hrdflt
        rw [exec_while_unfold (hlen := hlen)] at h
        generalize hBdef : bindOuts s args (inits.map (evalOpnd s)) = B at h hBr hbrdefs
        generalize hbrdef : (if evalCond c (B.rget ca) (B.rget cb) then body else dflt) = branch
          at h hbrdefs
        cases hbr : exec env stackLo f branch B with
        | none => rw [hbr] at h; exact absurd h (by simp)
        | some r' =>
          obtain ⟨s1, o1⟩ := r'
          have hs1 : s1.regs r = s.regs r := (ih branch B s1 o1 hbr r hbrdefs).trans hBr
          rw [hbr] at h
          cases o1 with
          | normal => exact absurd h (by simp)
          | ret vs => obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); exact hs1
          | brk k vs =>
            cases k with
            | zero =>
              by_cases hvs : (vs.length == outs.length) = true
              · simp only [hvs, if_true] at h
                obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
                exact (bindOuts_regs_not_mem outs vs s1 r hro).trans hs1
              · simp only [Bool.not_eq_true] at hvs; simp only [hvs] at h; exact absurd h (by simp)
            | succ k => obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); exact hs1
          | cont k vs =>
            cases k with
            | zero =>
              by_cases hvs : (vs.length == args.length) = true
              · simp only [hvs, if_true] at h
                exact (ih (.«while» outs (vs.map .const) args c ca cb body dflt) s1 s' oc h r
                  (by simpa only [defs, List.mem_append, not_or] using
                    ⟨⟨⟨hro, hrargs⟩, hrbody⟩, hrdflt⟩)).trans hs1
              · simp only [Bool.not_eq_true] at hvs; simp only [hvs] at h; exact absurd h (by simp)
            | succ k => obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); exact hs1
      · rw [exec_while_badlen (hlen := hlen)] at h; exact absurd h (by simp)
    | call f' argOps outs =>
      simp only [defs] at hr
      cases hlk : List.lookup f' env with
      | none => rw [exec_call_lookup_none (hlk := hlk)] at h; exact absurd h (by simp)
      | some fd =>
        by_cases harity : (argOps.length == fd.params.length && outs.length == fd.rvc) = true
        · cases hfe : frameEnter stackLo fd (argOps.map (evalOpnd s)) s.mem s.sp with
          | none => rw [exec_call_fe_none (hlk := hlk) (harity := harity) (hfe := hfe)] at h; exact absurd h (by simp)
          | some callee =>
            rw [exec_call_body (hlk := hlk) (harity := harity) (hfe := hfe)] at h
            cases hcb : exec env stackLo f fd.body callee with
            | none => rw [hcb] at h; exact absurd h (by simp)
            | some r' =>
              obtain ⟨s1, o1⟩ := r'; rw [hcb] at h
              cases o1 with
              | ret vs =>
                by_cases hrvc : (vs.length == fd.rvc) = true
                · simp only [hrvc, if_true] at h
                  obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h)
                  exact bindOuts_regs_not_mem outs vs _ r hr
                · simp only [Bool.not_eq_true] at hrvc; simp only [hrvc] at h; exact absurd h (by simp)
              | normal =>
                by_cases hrvc : (fd.rvc == 0) = true
                · simp only [hrvc, if_true] at h
                  obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj h); rfl
                · simp only [Bool.not_eq_true] at hrvc; simp only [hrvc] at h; exact absurd h (by simp)
              | brk k vs => exact absurd h (by simp)
              | cont k vs => exact absurd h (by simp)
        · rw [exec_call_arity_false (hlk := hlk) (harity := Bool.not_eq_true _ ▸ harity)] at h
          exact absurd h (by simp)

/-- `rget` form of the frame theorem (P2 corollary). -/
theorem exec_frame_rget (f : Nat) (stmt : Stmt) (s s' : St) (oc : Outcome)
    (h : exec env stackLo f stmt s = some (s', oc)) (r : Reg) (hr : r ∉ defs stmt) :
    s'.rget r = s.rget r := by
  unfold Prog.St.rget; split
  · rfl
  · exact exec_frame env stackLo f stmt s s' oc h r hr

/-! ### Byte-store memory rules (P3 support — the `Slice`/`Wf` borrow layer is
    reused from `LowIR.Ctrl.Hex0` in the proof files; these are the St-level
    facts it composes with). -/

theorem storeByte_mem_ne (s : St) (a a' : Word) (b : Byte) (h : a' ≠ a) :
    (s.storeByte a b).mem a' = s.mem a' := by
  show (if a' = a then b else s.mem a') = s.mem a'; rw [if_neg h]

theorem storeByte_mem_self (s : St) (a : Word) (b : Byte) :
    (s.storeByte a b).mem a = b := by
  show (if a = a then b else s.mem a) = b; rw [if_pos rfl]

end LowIR.SSA
