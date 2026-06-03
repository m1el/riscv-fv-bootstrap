#!/usr/bin/env python3
"""Collect Claude Code + Codex sessions for /var/data/bootstrap into ./sessions."""
import json, os, glob, re, getpass, subprocess, urllib.request
from datetime import datetime

PROJECT = "/var/data/bootstrap"
CLAUDE_DIR = os.path.expanduser("~/.claude/projects/-var-data-bootstrap")
CODEX_GLOB = os.path.expanduser("~/.codex/sessions/**/*.jsonl")
OUT = os.path.join(PROJECT, "sessions")
TOOL_TRUNC = 4000   # max chars per tool-result/output block in the transcript

# Redaction: applied to every byte written under sessions/ (transcripts + README).
# Targets are DISCOVERED at runtime (git identity + the OS user/home) so that no
# personal data is hard-coded — this script can itself be published next to the
# output without leaking what it redacts. Matched as literal substrings (no \b
# anchors) so even values embedded in quoted source/JSON inside a transcript are
# caught. Username is only redacted in home-path context (a bare "null" would
# clobber JSON `null`).
def _git_cfg(key):
    try:
        return subprocess.check_output(["git", "-C", PROJECT, "config", key],
                                       text=True, stderr=subprocess.DEVNULL).strip()
    except Exception:
        return ""

def build_redactions():
    reds = []
    email = _git_cfg("user.email")
    name = _git_cfg("user.name")
    home = os.path.expanduser("~")
    try:
        user = getpass.getuser()
    except Exception:
        user = ""
    if email:
        reds.append((re.compile(re.escape(email)), "<redacted-email>"))
    if name:
        reds.append((re.compile(re.escape(name)), "<redacted-name>"))
    if home and home not in ("~", "/"):
        reds.append((re.compile(re.escape(home)), "/home/<user>"))
    elif user:
        reds.append((re.compile(re.escape(f"/home/{user}")), "/home/<user>"))
    return reds

REDACTIONS = build_redactions()

def redact(s):
    if not isinstance(s, str):
        return s
    for pat, repl in REDACTIONS:
        s = pat.sub(repl, s)
    return s

def jlines(path):
    with open(path, encoding="utf-8") as f:
        for ln in f:
            ln = ln.strip()
            if not ln:
                continue
            try:
                yield json.loads(ln)
            except Exception:
                continue

def trunc(s, n=TOOL_TRUNC):
    s = s if isinstance(s, str) else json.dumps(s, ensure_ascii=False)
    if len(s) > n:
        return s[:n] + f"\n… [truncated {len(s)-n} chars]"
    return s

def fmt_ts(ts):
    if not ts:
        return "?"
    try:
        return datetime.fromisoformat(ts.replace("Z", "+00:00")).strftime("%Y-%m-%d %H:%M:%SZ")
    except Exception:
        return ts

def first_prompt(text_blocks):
    """First human prompt that isn't a tag wrapper / caveat / system reminder."""
    for t in text_blocks:
        s = t.strip()
        if not s:
            continue
        # skip XML-ish wrappers (system-reminder, command-*, local-command-caveat,
        # environment_context, …) and command caveats / interrupt markers
        if s[0] == "<" or s.startswith("Caveat:") or s.startswith("[Request interrupted"):
            continue
        return s
    return text_blocks[0].strip() if text_blocks else ""

# ----------------------------------------------------------------- Claude
def parse_claude(path):
    sid = os.path.basename(path).replace(".jsonl", "")
    models, n_user, n_tool = set(), 0, 0
    tok = dict(input=0, output=0, cache_create=0, cache_read=0)
    usage_by_req = {}          # requestId -> usage (dedupe split-block lines)
    first_ts = last_ts = None
    user_prompts, last_assistant_text = [], ""
    lines = []
    cur_rid, cur_body = None, []   # group consecutive same-requestId assistant blocks into one turn

    def flush_turn():
        if cur_body:
            lines.append("### 🤖 **Assistant**\n\n" + "\n\n".join(cur_body) + "\n")

    for d in jlines(path):
        typ = d.get("type")
        ts = d.get("timestamp")
        if ts:
            first_ts = first_ts or ts
            last_ts = ts
        if typ not in ("user", "assistant"):
            continue
        msg = d.get("message", {}) or {}
        role = msg.get("role", typ)
        content = msg.get("content")
        blocks = content if isinstance(content, list) else [{"type": "text", "text": content}]
        text_blocks, rendered = [], []
        for b in blocks:
            if not isinstance(b, dict):
                rendered.append(str(b)); continue
            bt = b.get("type")
            if bt == "text":
                txt = b.get("text") or ""
                text_blocks.append(txt); rendered.append(txt)
            elif bt == "thinking":
                rendered.append("> 💭 (thinking)\n> " + trunc(b.get("thinking",""),1500).replace("\n","\n> "))
            elif bt == "tool_use":
                n_tool += 1
                rendered.append(f"**🔧 tool → {b.get('name')}**\n```json\n{trunc(b.get('input',{}),1500)}\n```")
            elif bt == "tool_result":
                c = b.get("content")
                if isinstance(c, list):
                    c = "\n".join(x.get("text","") if isinstance(x,dict) else str(x) for x in c)
                rendered.append(f"**↩︎ tool result**\n```\n{trunc(c)}\n```")
        if role == "assistant":
            if msg.get("model"):
                models.add(msg["model"])
            rid = d.get("requestId") or d.get("uuid")
            u = msg.get("usage")
            if u and rid not in usage_by_req:     # count usage once per API request
                usage_by_req[rid] = u
            jointext = "\n".join(text_blocks).strip()
            if jointext:
                last_assistant_text = jointext
            if rid != cur_rid:                     # new turn -> flush previous
                flush_turn(); cur_rid, cur_body = rid, []
            cur_body.extend(r for r in rendered if r.strip())
        else:
            flush_turn(); cur_rid, cur_body = None, []
            n_user += 1
            for t in text_blocks:
                if t.strip():
                    user_prompts.append(t)
            body = "\n\n".join(r for r in rendered if r.strip())
            if body.strip():
                lines.append(f"### 👤 **User**\n\n{body}\n")
    flush_turn()
    for u in usage_by_req.values():
        tok["input"] += u.get("input_tokens", 0) or 0
        tok["output"] += u.get("output_tokens", 0) or 0
        tok["cache_create"] += u.get("cache_creation_input_tokens", 0) or 0
        tok["cache_read"] += u.get("cache_read_input_tokens", 0) or 0
    return dict(agent="claude", sid=sid, path=path, models=sorted(models),
                n_assist=len(usage_by_req), n_user=n_user, n_tool=n_tool, tok=tok,
                first_ts=first_ts, last_ts=last_ts,
                title=first_prompt(user_prompts),
                first_prompt=first_prompt(user_prompts),
                last_text=last_assistant_text, transcript="\n".join(lines))

# ----------------------------------------------------------------- Codex
def parse_codex(path):
    sid = cwd = model = first_ts = last_ts = None
    n_user = n_assist = n_tool = 0
    tok_info = None
    user_prompts, last_assistant_text, lines = [], "", []
    for d in jlines(path):
        typ = d.get("type"); p = d.get("payload", {}) or {}
        ts = d.get("timestamp")
        if ts:
            first_ts = first_ts or ts; last_ts = ts
        if typ == "session_meta":
            sid = p.get("id"); cwd = p.get("cwd"); first_ts = p.get("timestamp") or first_ts
        elif typ == "turn_context":
            model = model or p.get("model"); cwd = cwd or p.get("cwd")
        elif typ == "event_msg" and p.get("type") == "token_count":
            info = p.get("info")
            if info and info.get("total_token_usage"):
                tok_info = info["total_token_usage"]
        elif typ == "event_msg" and p.get("type") == "user_message":
            m = p.get("message")
            if isinstance(m, str) and m.strip():
                user_prompts.append(m)
        elif typ == "response_item":
            pt = p.get("type")
            if pt == "message":
                role = p.get("role", "?")
                txt = "".join(c.get("text","") for c in (p.get("content") or []) if isinstance(c, dict))
                if not txt.strip():
                    continue
                if role == "user":
                    n_user += 1; user_prompts.append(txt)
                    lines.append(f"### 👤 **User**\n\n{txt}\n")
                elif role == "assistant":
                    n_assist += 1; last_assistant_text = txt.strip()
                    lines.append(f"### 🤖 **Assistant**\n\n{txt}\n")
                else:  # developer / system
                    lines.append(f"### ⚙️ **{role}**\n\n{trunc(txt,1500)}\n")
            elif pt == "reasoning":
                summ = p.get("summary") or []
                rt = "\n".join(x.get("text","") if isinstance(x,dict) else str(x) for x in summ) if isinstance(summ,list) else str(summ)
                if rt.strip():
                    lines.append("> 💭 (reasoning)\n> " + trunc(rt,1500).replace("\n","\n> ") + "\n")
            elif pt == "function_call":
                n_tool += 1
                lines.append(f"**🔧 call → {p.get('name')}**\n```\n{trunc(p.get('arguments',''),1500)}\n```")
            elif pt == "function_call_output":
                out = p.get("output")
                if isinstance(out, dict):
                    out = out.get("content", out)
                lines.append(f"**↩︎ output**\n```\n{trunc(out)}\n```")
    # normalize codex tokens to common shape
    tok = dict(input=0, output=0, cache_create=0, cache_read=0, reasoning=0, total=0)
    if tok_info:
        tok["input"] = tok_info.get("input_tokens", 0)
        tok["cache_read"] = tok_info.get("cached_input_tokens", 0)
        tok["output"] = tok_info.get("output_tokens", 0)
        tok["reasoning"] = tok_info.get("reasoning_output_tokens", 0)
        tok["total"] = tok_info.get("total_tokens", 0)
    # codex input_tokens is the full prompt incl. cached; expose non-cached for parity
    return dict(agent="codex", sid=sid or os.path.basename(path), path=path, models=[model] if model else [],
                cwd=cwd, n_assist=n_assist, n_user=n_user, n_tool=n_tool, tok=tok,
                first_ts=first_ts, last_ts=last_ts,
                title=first_prompt(user_prompts), first_prompt=first_prompt(user_prompts),
                last_text=last_assistant_text, transcript="\n".join(lines))

# ----------------------------------------------------------------- write
# ----------------------------------------------------------------- pricing
OPENROUTER_URL = "https://openrouter.ai/api/v1/models"
PRICE_CACHE = os.path.join(OUT, "openrouter_models.json")
PRICING = {}   # {"exact": {id: rates}, "base": {canon: (id, rates)}, "src": str}

def _canon(s):
    return re.sub(r"[^a-z0-9]", "", s.lower())

def load_pricing():
    """Fetch OpenRouter model pricing (USD/token); cache to disk for offline reruns."""
    raw = src = None
    try:
        req = urllib.request.Request(OPENROUTER_URL, headers={"User-Agent": "sessions-collector"})
        raw = json.load(urllib.request.urlopen(req, timeout=30))
        os.makedirs(OUT, exist_ok=True)
        json.dump(raw, open(PRICE_CACHE, "w"))
        src = "openrouter.ai/api/v1/models (live)"
    except Exception as e:
        if os.path.exists(PRICE_CACHE):
            raw = json.load(open(PRICE_CACHE)); src = f"{PRICE_CACHE} (cache; live fetch failed: {e})"
        else:
            print("WARN: pricing unavailable (fetch failed, no cache):", e)
            return {"exact": {}, "base": {}, "src": None}
    exact, base = {}, {}
    for m in raw.get("data", []):
        mid = m["id"].lstrip("~")
        p = m.get("pricing", {}) or {}
        def g(k):
            try: return float(p[k])
            except Exception: return None
        rates = dict(prompt=g("prompt"), completion=g("completion"),
                     cache_read=g("input_cache_read"), cache_write=g("input_cache_write"))
        exact[mid.lower()] = rates
        base.setdefault(_canon(mid.split("/")[-1]), (mid, rates))
    return {"exact": exact, "base": base, "src": src}

def match_pricing(model):
    """Map a recorded model name to an OpenRouter id + rates. Returns (id, rates) or (None, None)."""
    if not PRICING or not model:
        return None, None
    ml = model.lower()
    if ml in PRICING["exact"]:
        return model, PRICING["exact"][ml]
    cb = _canon(model.split("/")[-1])
    if cb in PRICING["base"]:
        return PRICING["base"][cb]
    return None, None

def session_cost(sess):
    """USD cost from matched OpenRouter rates, or None if no pricing matched."""
    rates = sess.get("priced")
    if not rates:
        return None
    t = sess["tok"]
    prm = rates["prompt"] or 0.0
    cmp = rates["completion"] or 0.0
    cr  = rates["cache_read"]  if rates["cache_read"]  is not None else prm
    cw  = rates["cache_write"] if rates["cache_write"] is not None else prm
    if sess["agent"] == "claude":
        return t["input"]*prm + t["cache_create"]*cw + t["cache_read"]*cr + t["output"]*cmp
    # codex: input_tokens already includes cached; output_tokens already includes reasoning
    fresh = max(0, t["input"] - t["cache_read"])
    return fresh*prm + t["cache_read"]*cr + t["output"]*cmp

def file_stamp(sess):
    """yyyy-mm-dd_hh-mm from the session start (fallback: source-file mtime)."""
    ts = sess.get("first_ts")
    if ts:
        try:
            return datetime.fromisoformat(ts.replace("Z", "+00:00")).strftime("%Y-%m-%d_%H-%M")
        except Exception:
            pass
    try:
        return datetime.fromtimestamp(os.path.getmtime(sess["path"])).strftime("%Y-%m-%d_%H-%M")
    except Exception:
        return "0000-00-00_00-00"

def write_session(sess, subdir):
    d = os.path.join(OUT, subdir)
    os.makedirs(d, exist_ok=True)
    hexid = re.sub(r"[^0-9a-f]", "", sess["sid"].lower())[:12]   # 12 hex chars disambiguates
    fn = os.path.join(d, f"{file_stamp(sess)}_{hexid}.md")
    t = sess["tok"]
    cost = sess.get("cost")
    pid = sess.get("priced_id")
    r = sess.get("priced")
    if r:
        rate_note = (f"priced as `{pid}` — ${ (r['prompt'] or 0)*1e6:g}/$"
                     f"{ (r['completion'] or 0)*1e6:g} in/out per Mtok"
                     + (f", ${r['cache_read']*1e6:g} cache-read" if r['cache_read'] is not None else "")
                     + (f", ${r['cache_write']*1e6:g} cache-write" if r['cache_write'] is not None else ""))
        cost_s = f"**${cost:,.2f}**" if cost is not None else "n/a"
    else:
        rate_note = f"no OpenRouter pricing match for model `{', '.join(sess['models']) or '?'}`"
        cost_s = "n/a"
    if sess["agent"] == "claude":
        tokline = (f"- output: **{t['output']:,}**  |  fresh input: {t['input']:,}  |  "
                   f"cache write: {t['cache_create']:,}  |  cache read: {t['cache_read']:,}\n"
                   f"- **cost: {cost_s}** ({rate_note})")
    else:
        tokline = (f"- output: **{t['output']:,}** (reasoning {t['reasoning']:,})  |  "
                   f"input incl. cached: {t['input']:,}  (cached {t['cache_read']:,})  |  "
                   f"total: {t['total']:,}\n"
                   f"- **cost: {cost_s}** ({rate_note})")
    parts = [
        f"# {sess['agent'].title()} session `{sess['sid']}`\n\n",
        f"- **Agent:** {sess['agent']}\n",
        f"- **Model(s):** {', '.join(sess['models']) or '?'}\n",
        f"- **Started:** {fmt_ts(sess['first_ts'])}  |  **Last activity:** {fmt_ts(sess['last_ts'])}\n",
        f"- **Turns:** {sess['n_user']} user / {sess['n_assist']} assistant  |  **Tool calls:** {sess['n_tool']}\n",
        f"- **Source:** `{sess['path']}`\n\n",
        "## Token cost\n\n" + tokline + "\n\n",
        "## Summary\n\n",
        f"**First request:**\n\n> {trunc(sess['first_prompt'],600).strip().replace(chr(10),chr(10)+'> ')}\n\n",
        f"**Final response:**\n\n> {trunc(sess['last_text'],600).strip().replace(chr(10),chr(10)+'> ')}\n\n",
        "---\n\n## Transcript\n\n",
        sess["transcript"] or "_(no message content)_\n",
    ]
    with open(fn, "w", encoding="utf-8") as f:
        f.write(redact("".join(parts)))   # redact whole file (catches Source path, prompts, tool output)
    return fn

def main():
    global PRICING
    PRICING = load_pricing()
    print("pricing source:", PRICING.get("src"))
    sessions = []
    for p in sorted(glob.glob(os.path.join(CLAUDE_DIR, "*.jsonl"))):
        sessions.append(parse_claude(p))
    for p in glob.glob(CODEX_GLOB, recursive=True):
        # cheap cwd filter
        try:
            head = open(p, encoding="utf-8").read(4000)
        except Exception:
            continue
        if f'"cwd":"{PROJECT}"' in head:
            sessions.append(parse_codex(p))
    sessions.sort(key=lambda s: s["first_ts"] or "")
    # price each session against OpenRouter rates
    for s in sessions:
        pid, rates = match_pricing(s["models"][0] if s["models"] else None)
        s["priced_id"], s["priced"] = pid, rates
        s["cost"] = session_cost(s)
    # write per-session files
    rows = []
    for s in sessions:
        fn = write_session(s, s["agent"])   # subdir = "claude" | "codex"
        s["file"] = os.path.relpath(fn, OUT)
        rows.append(s)
    # aggregate
    cl = [s for s in rows if s["agent"]=="claude"]
    cx = [s for s in rows if s["agent"]=="codex"]
    def agg(group):
        return (sum(s["tok"]["output"] for s in group),
                sum((s["cost"] or 0) for s in group),
                all(s["cost"] is not None for s in group if s["n_assist"]))
    cl_out, cl_cost, cl_full = agg(cl)
    cx_out, cx_cost, cx_full = agg(cx)
    priced_models = sorted({f"{s['models'][0]} → `{s['priced_id']}`"
                            for s in rows if s.get("priced_id")})
    R = []
    R.append("# Agent sessions for `/var/data/bootstrap`\n\n")
    R.append(f"Collected **{len(cl)} Claude Code** session(s) and **{len(cx)} Codex** session(s) "
             f"whose working directory is this project.\n\n")
    R.append("Per-session transcripts, summaries, and token costs live under `claude/` and `codex/`. "
             "Each file has a header (model, turns, token cost), a summary (first request + final "
             "response), and the full transcript (long tool outputs truncated). Personal name, email, "
             "and OS username are redacted.\n\n")
    R.append("## Aggregate cost\n\n")
    R.append("| Agent | Sessions | Output tokens | Cost (USD) |\n|---|--:|--:|--:|\n")
    R.append(f"| Claude Code | {len(cl)} | {cl_out:,} | **${cl_cost:,.2f}** |\n")
    R.append(f"| Codex | {len(cx)} | {cx_out:,} | **${cx_cost:,.2f}** |\n")
    R.append(f"| **All** | **{len(cl)+len(cx)}** | **{cl_out+cx_out:,}** | **${cl_cost+cx_cost:,.2f}** |\n\n")
    R.append(f"> **Pricing source:** {PRICING.get('src') or 'unavailable'}. Cost is computed per token "
             "from each model's OpenRouter rates (prompt / completion / cache-read / cache-write), so "
             "cache-read tokens — re-counted every turn — are billed at their reduced rate rather "
             "than inflating the headline. Model rate matches:\n>\n")
    for pm in priced_models:
        R.append(f"> - {pm}\n")
    R.append(">\n> **Caveat on Codex cached tokens (lower bound):** the rollout records the *agent-reported* "
             "`cached_input_tokens`, i.e. how many input tokens Codex *expected* to hit the provider cache. "
             "Actual billing only discounts tokens that genuinely hit the cache (entries expire on a TTL), "
             "so the rest are billed at the full prompt rate. This bites models with a steep cache discount: "
             "e.g. `deepseek-v4-pro` lists cache-read at $0.0036/Mtok, but its real charge here (~$0.36) "
             "implies an effective ~$0.30/Mtok (≈⅓ of the 'cached' tokens actually hit). OpenAI caching "
             "reconciled exactly. Codex costs below are therefore a **lower bound**; Claude (whose cache "
             "reads are reported as billed) is exact.\n")
    R.append("\n")
    for label, group in (("Claude Code", cl), ("Codex", cx)):
        R.append(f"## {label} sessions\n\n")
        R.append("| # | Date | Model | Turns | Tools | Output tok | Cost | First request | File |\n")
        R.append("|--|---|---|--:|--:|--:|--:|---|---|\n")
        for i, s in enumerate(group, 1):
            t = s["tok"]
            metric = f"${s['cost']:,.2f}" if s["cost"] is not None else "n/a"
            req = (s["first_prompt"] or "").replace("\n"," ").replace("|","\\|")[:60]
            R.append(f"| {i} | {fmt_ts(s['first_ts'])[:16]} | {', '.join(s['models']) or '?'} | "
                     f"{s['n_user']}/{s['n_assist']} | {s['n_tool']} | {t['output']:,} | {metric} | "
                     f"{req} | [`{s['file']}`]({s['file']}) |\n")
        R.append("\n")
    with open(os.path.join(OUT, "README.md"), "w", encoding="utf-8") as f:
        f.write(redact("".join(R)))
    print(f"Wrote {len(rows)} sessions to {OUT}")
    print(f"Claude: {len(cl)} sessions · output {cl_out:,} · ${cl_cost:,.2f}")
    print(f"Codex : {len(cx)} sessions · output {cx_out:,} · ${cx_cost:,.2f}")
    print(f"TOTAL : ${cl_cost+cx_cost:,.2f}")

if __name__ == "__main__":
    main()
