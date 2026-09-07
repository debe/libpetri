# petri-net-design

A skill that teaches net *design* rather than API calls: data carried as tokens, decisions as
topology, budgets and permits as places, reusable subnets, correlated fork and join by identity,
and how to keep SMT and state-class proofs cheap as a net grows. It is language agnostic, with a
short appendix per implementation for the handful of facts that change a design decision.

It works in **Claude Code, OpenAI Codex CLI, opencode and oh-my-pi**. All four read the same
`SKILL.md` contract, so there is one copy of the content and no per-harness fork.

## What is in it

| File | Read it for |
|---|---|
| `skills/petri-net-design/SKILL.md` | the principles and the closing decision checklist. Always loaded. |
| `references/verification.md` | any proof question: what is checkable, why a query is `Unknown`, keeping proofs cheap |
| `references/composition.md` | subnets, ports versus channels, instantiate versus direct compose, fusion |
| `references/nu-nets.md` | correlating parallel work by identity: minting, matching, the budget place |
| `references/patterns.md` | worked topologies from a production system, and what made them provable |
| `references/lang-{java,typescript,rust,python}.md` | the per-language facts that change a design decision |

The references load on demand, so a session that never asks a proof question never pays for
`verification.md`.

## Install

### Codex, opencode and oh-my-pi

All three read `~/.agents/skills`, so one symlink installs it in all three:

```bash
git clone --depth 1 https://github.com/debe/libpetri.git ~/.local/share/libpetri
mkdir -p ~/.agents/skills
ln -s ~/.local/share/libpetri/plugins/libpetri/skills/petri-net-design \
      ~/.agents/skills/petri-net-design
```

**Updating is `git -C ~/.local/share/libpetri pull`.** The symlink means there is nothing else to
do, which is the whole reason this is a link rather than a copy.

**Uninstall** is `rm ~/.agents/skills/petri-net-design`.

### Claude Code

```
/plugin marketplace add debe/libpetri
/plugin install libpetri@libpetri
```

Invoke it directly with `/libpetri:petri-net-design`. From inside a checkout, use
`/plugin marketplace add .` instead of the GitHub shorthand.

### Per-harness alternatives

Use these only if `~/.agents/skills` is not picked up, for instance because you turned that
discovery root off.

**Codex** reads `$CODEX_HOME/skills`:

```bash
ln -s ~/.local/share/libpetri/plugins/libpetri/skills/petri-net-design \
      ~/.codex/skills/petri-net-design
```

**opencode** reads its own config dir, or takes an explicit path:

```bash
ln -s ~/.local/share/libpetri/plugins/libpetri/skills/petri-net-design \
      ~/.config/opencode/skills/petri-net-design
```

```json
{
  "$schema": "https://opencode.ai/config.json",
  "skills": { "paths": ["/absolute/path/to/libpetri/plugins/libpetri/skills"] }
}
```

**oh-my-pi** reads its agent dir, or `skills.customDirectories` in `~/.omp/agent/config.yml`:

```bash
ln -s ~/.local/share/libpetri/plugins/libpetri/skills/petri-net-design \
      ~/.omp/agent/skills/petri-net-design
```

```yaml
skills:
  customDirectories:
    - /absolute/path/to/libpetri/plugins/libpetri/skills
```

## Inside a libpetri checkout

Nothing to install. `.agents/skills/petri-net-design` is a committed relative symlink to
`plugins/libpetri/skills/petri-net-design`, and Codex, opencode and oh-my-pi all read a repo-local
`.agents/skills`, so the skill is available to all three as soon as you open the repo. Claude Code
users take the plugin route above.

## Verify it loaded

**Codex** renders the model-visible prompt, no model call and no network:

```bash
codex debug prompt-input "x" | grep -c petri-net-design     # expect 1
codex debug prompt-input "x" | grep -A5 'Skill roots'       # shows which root won
```

**opencode**: redirect to a file, do not pipe. `opencode debug skill` emits about 64 KB and
truncates nondeterministically through a pipe, which makes `| jq` fail with
`Unfinished string at EOF` and makes `| grep -c` return a different number each run:

```bash
opencode debug skill > /tmp/skills.json && grep -c petri-net-design /tmp/skills.json
```

**oh-my-pi** has no offline probe. Ask it, or use the slash command in an interactive session:

```bash
omp -p "Without using any tools, list the names of every skill available to you."
```

```
/skill:petri-net-design
```

`omp read skill://petri-net-design` looks like the right probe and is not: the `read` CLI does not
populate the skill registry, so it reports `Unknown skill` even when the skill loads correctly in
a session.

**Claude Code**, offline and exit-coded:

```bash
claude plugin validate plugins/libpetri
claude plugin details libpetri@libpetri     # component inventory and projected token cost
```

## Windows and symlinks

`.agents/skills/petri-net-design` is a git symlink. On Windows it only materialises if
`git config --global core.symlinks true` is set **and** Developer Mode is enabled, both before
cloning; a GitHub "Download ZIP" never materialises symlinks on any platform. If
`.agents/skills/petri-net-design` is a small text file rather than a directory, that is why, and
the skill will not load in Codex, opencode or oh-my-pi. Either re-clone with the setting above, or
install into `~/.agents/skills` as in the Install section, which needs no symlink from the repo.

`scripts/check-agent-skills.py` fails loudly on exactly this, so a checkout that flattened the
link cannot be committed back over it.

## How this is packaged

The canonical content lives in `skills/petri-net-design/` and nothing copies it. The repo-local
`.agents/skills/petri-net-design` is a relative symlink, so drift between harnesses is impossible
by construction.

Three constraints are load bearing, because the harnesses disagree on how strictly they enforce
them and the strictest one fails silently:

- `name` must match `^[a-z0-9]+(-[a-z0-9]+)*$` **and** equal the directory name (opencode).
- `description` must be 1 to 1024 characters (opencode). Codex additionally budgets the whole
  skills list at 2% of the context window, so a long description crowds out other skills.
- A skill sits exactly one level under a skills root. `skills/group/name/SKILL.md` is invisible to
  oh-my-pi.

Run `python3 scripts/check-agent-skills.py` before pushing; CI runs it too. `claude plugin
validate` does **not** catch the description limit, which is why the script exists.

`skills/petri-net-design/evals/evals.json` is a `skill-creator` LLM-judge rubric. It is not wired
into `claude plugin eval`, which expects `case.yaml` or `prompt.md` plus `graders/`.
