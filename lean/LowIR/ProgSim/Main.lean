/-
  LowIR.ProgSim.Main — Phase 6, the `prog_sim` summit.

  Assembles the whole campaign: the compiled RV64I blob computes what the D7/D8
  IL says `entry(args)` computes. The proof decomposes as

    prog_sim  =  entry_run_sim  ∘  runFuel_eq_stepN

  where `entry_run_sim` is the machine run in plain-iteration (`stepN`) form —
  stub `jal` → `entry`'s prologue (`prologue_sim`) → body (`lower_sim_cf`, fed
  `hfn` from `fn_hfn` and the flat obligations from `SimPre` + the layout) →
  epilogue (`epilogue_sim`) → halt — and `runFuel_eq_stepN` bridges plain
  iteration to the halt-checking `runFuel` the statement uses (RESUME-PROGSIM
  §3.2: prove with `step^[k]`, convert at the top).
-/
import LowIR.ProgSim.LayoutFacts

namespace LowIR.ProgSim

open Rv64i (Instr State step Word decode fetch32 runFuel)
open LowIR.Ctrl (Outcome)
open LowIR.Prog (St Program Name FunDef installData frameEnter dbaseOf)
open LowIR.Compile (userOff)

/-! ## The `stepN` ↔ `runFuel` bridge. -/

/-- If the machine first reaches `halt` at exactly step `K`, plain iteration and
    the halt-checking `runFuel` agree at `K`. (The `hne` clause — `halt` not hit
    before `K` — is what `entry_run_sim` supplies: the only instruction at
    `codeBase+4` is the halt loop, reached solely by `entry`'s final `jalr`.) -/
theorem runFuel_eq_stepN (halt : Word) (K : Nat) (m : State)
    (hne : ∀ j, j < K → (stepN j m).pc ≠ halt) :
    runFuel halt K m = stepN K m := by
  induction K generalizing m with
  | zero => rfl
  | succ K ih =>
      have h0 : m.pc ≠ halt := hne 0 (by omega)
      have hstep : ∀ j, j < K → (stepN j (step m)).pc ≠ halt := fun j hj => by
        rw [← stepN_succ]; exact hne (j + 1) (by omega)
      rw [runFuel, if_neg h0, ih (step m) hstep, stepN_succ]

/-! ## The machine-side summit (`stepN` form). -/

/-- **`entry_run_sim`** — from the initial state, the machine runs the stub
    `jal`, `entry`'s prologue/body/epilogue, and halts at `codeBase+4` with
    `entry`'s returns in `a0..` and memory agreeing off the blob and the stack.
    The final `hne` conjunct records that `halt` is reached ONLY at the end
    (feeding `runFuel_eq_stepN`).

    PROOF DEFERRED — the remaining summit work, all atoms in hand:
    · stub step: `stub_emitted` + `step_jal` (m0 ↦ m1 at `codeBase + fnPos
      entry`, `ra := codeBase+4`, `sp = sp0`, args in `a0..`);
    · `prologue_sim` at m1 (frameEnter unfolded — `hcsp`/`hcrg` from `run_inv`'s
      `st0`, holes `[]`);
    · `lower_sim_cf` on `fd.body` (`hfn` ← `fn_hfn`; `hem` at the prologue end;
      `hdat`/`hdbase`/`hdpos`/`hpad`/`halign`/`hblob`/`hbd` ← `SimPre` + layout);
      `oc ∈ {normal, ret}` (from `run_inv`) both land at `epiPos`;
    · `epilogue_sim` (rets → `a0..`, restore, `jalr` to `ra = codeBase+4`); s' IS
      the body state (`run` doesn't remarshal), so `rget (10+j) = s'.rget rets[j]`
      matches directly;
    · `hne`: `fnPos entry ≥ 8 > 4`, so pc stays `> codeBase+4` until the final
      `jalr`. -/
theorem entry_run_sim
    {P : Program} {entry : Name} {fd : FunDef} {args : List Word}
    {sp0 : Word} {fuel : Nat} {s' : St} {L : Layout} {m0 : State}
    (hlk    : List.lookup entry P.env = some fd)
    (hL     : layoutOf P entry L.codeBase L.stackLo = some L)
    (hpre   : SimPre L L.stackLo sp0)
    (hpc    : m0.pc = L.codeBase)
    (hsp    : m0.rget 2 = sp0)
    (hargc  : args.length = fd.argc)
    (hargs  : ∀ i, i < fd.argc → m0.rget (10 + i) = args.getD i 0)
    (hinst  : Installed L m0)
    (hbr    : ∀ g gd, List.lookup g P.env = some gd → BranchOk gd.body)
    (haccess : ∀ st0,
                frameEnter L.stackLo fd (userPad P.env entry) args
                    (installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0)) sp0
                  = some st0 →
                MemAccOff L [(st0.sp, userOff fd)] P
                  (dbaseOf (L.codeBase + BitVec.ofNat 64 L.segStart) P.data)
                  (userPad P.env) L.stackLo fuel fd.body st0)
    (hmem   : ∀ a, ¬ MachPriv L [] a →
                installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0) a
                  = m0.mem a)
    (hrun   : LowIR.Prog.run P L.stackLo fuel entry args (fun _ => 0) sp0
                (userPad P.env) (L.codeBase + BitVec.ofNat 64 L.segStart) = some s') :
    ∃ K, (stepN K m0).pc = L.haltPc
       ∧ (∀ j, j < fd.rvc → (stepN K m0).rget (10 + j) = s'.rget (fd.rets.toList.getD j 0))
       ∧ (∀ a, ¬ memRange a L.codeBase L.blobLen → ¬ MachStack L.stackLo sp0 a →
            s'.mem a = (stepN K m0).mem a)
       ∧ (∀ j, j < K → (stepN j m0).pc ≠ L.haltPc) := by
  sorry

/-! ## The summit. -/

/-- **`prog_sim`** (RESUME-PROGSIM §3.3) — if the D7/D8 IL says `entry(args)`
    computes `s'` (with the P1 padding `userPad`), the compiled RV64I blob,
    started at `codeBase` with `args` in `a0..` and `sp = sp0`, runs to the halt
    pad in a state whose `a0..` hold `entry`'s returns and whose memory agrees
    with `s'` off the blob and the stack. Assembles `entry_run_sim` with the
    `runFuel_eq_stepN` bridge. -/
theorem prog_sim
    {P : Program} {entry : Name} {fd : FunDef} {args : List Word}
    {sp0 : Word} {fuel : Nat} {s' : St} {L : Layout} {m0 : State}
    (hlk    : List.lookup entry P.env = some fd)
    (hL     : layoutOf P entry L.codeBase L.stackLo = some L)
    (hpre   : SimPre L L.stackLo sp0)
    (hpc    : m0.pc = L.codeBase)
    (hsp    : m0.rget 2 = sp0)
    (hargc  : args.length = fd.argc)
    (hargs  : ∀ i, i < fd.argc → m0.rget (10 + i) = args.getD i 0)
    (hinst  : Installed L m0)
    (hbr    : ∀ g gd, List.lookup g P.env = some gd → BranchOk gd.body)
    (haccess : ∀ st0,
                frameEnter L.stackLo fd (userPad P.env entry) args
                    (installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0)) sp0
                  = some st0 →
                MemAccOff L [(st0.sp, userOff fd)] P
                  (dbaseOf (L.codeBase + BitVec.ofNat 64 L.segStart) P.data)
                  (userPad P.env) L.stackLo fuel fd.body st0)
    (hmem   : ∀ a, ¬ MachPriv L [] a →
                installData (L.codeBase + BitVec.ofNat 64 L.segStart) P.data (fun _ => 0) a
                  = m0.mem a)
    (hrun   : LowIR.Prog.run P L.stackLo fuel entry args (fun _ => 0) sp0
                (userPad P.env) (L.codeBase + BitVec.ofNat 64 L.segStart) = some s') :
    ∃ k, (runFuel L.haltPc k m0).pc = L.haltPc
       ∧ (∀ j, j < fd.rvc →
            (runFuel L.haltPc k m0).rget (10 + j) = s'.rget (fd.rets.toList.getD j 0))
       ∧ (∀ a, ¬ memRange a L.codeBase L.blobLen → ¬ MachStack L.stackLo sp0 a →
            s'.mem a = (runFuel L.haltPc k m0).mem a) := by
  obtain ⟨K, hHalt, hRets, hMem, hne⟩ :=
    entry_run_sim hlk hL hpre hpc hsp hargc hargs hinst hbr haccess hmem hrun
  have hbridge := runFuel_eq_stepN L.haltPc K m0 hne
  exact ⟨K, by rw [hbridge]; exact hHalt,
             fun j hj => by rw [hbridge]; exact hRets j hj,
             fun a h1 h2 => by rw [hbridge]; exact hMem a h1 h2⟩

end LowIR.ProgSim
