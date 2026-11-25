# Credits

How this formalization was made, from the run log and the session transcripts. Times are America/Chicago (UTC−06:00).

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization, chose the paper and its published
  version, and decided the layout in the collection rooted at lean4-phylogenetics. He decided that the semidirected
  networks move to lean4-phylogenetics before the statements were written, that lean4-allman2011 joins the collection so
  that this repository proves the results of Allman, Degnan and Rhodes 2011 from it, and that Proposition 13 is
  formalized in a corrected form together with a refutation of the printed statement.
- **Formalization:** Claude Code 2.1.331 (VS Code extension) with Claude Opus 5.5 (`claude-opus-5-5`), for the
  statements, the proofs, the audit and the documents: one session, with sub-agents. Every model call of the round was to
  `claude-opus-5-5`. There was no earlier draft.
- **Procedure:** the [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) skill, version 4.6.3 (the
  local copy, whose files were updated during the round), under the collection's conventions (lean4-phylogenetics,
  `docs/CONVENTIONS.md`).
- **Review:** no person has reviewed the proofs. Independent agents (`claude-opus-5-5`), which did not write what they
  checked, reviewed:
  - the statements of the library against the paper (2026-11-24, 19:11–19:32), which found Proposition 13 false as
    printed and two formal statements that did not yet say what the paper says;
  - the Challenge, twice (19:42–20:00, and 2026-11-25, 03:29–03:43), recomputing equation (1) and Examples 6 and 7 from
    its definitions;
  - the formal proofs against the paper's: Sections 2–5 and the Appendix (02:46–02:59), Sections 6–7 (02:46–02:55),
    Sections 8–9 (03:29–03:40), and the revised proofs of Theorem 4, Lemma 16 and Proposition 13 (04:19–04:29);
  - the literature, searched on 2026-11-24 (23:06–23:27) and checked again for the report on 2026-11-25.

  The agent that wrote the report checked every finding against the paper's text and the TeX source of arXiv v1.
- **Code of other projects:** none is copied into this repository. The libraries lean4-phylogenetics,
  lean4-phylo-network and lean4-allman2011 are required at pinned commits ([`lakefile.toml`](../../lakefile.toml)); the semidirected
  networks of lean4-phylogenetics come from lean4-allman2023. The scripts in [`scripts/`](../../scripts) come from the
  formalize-math-paper skill (Apache-2.0, by the same author), [`scripts/Audit.lean`](../../scripts/Audit.lean) from its template and
  [`scripts/linkify_docs.py`](../../scripts/linkify_docs.py) as lean4-tinnik configures it.

## The formalization (2026-11-24 to 2026-11-25)

How it was made:

- **Setup** (18:29–18:40): the published version chosen, the TeX of arXiv v1 compared with it, the configuration
  recorded. At the maintainer's decision, the semidirected networks moved first to lean4-phylogenetics, which this
  repository requires.
- **Statements** (to 19:36): every definition and numbered result stated, with the routes of the paper's proofs
  extracted from the TeX; then the Challenge (to 20:01). Both were reviewed independently before the proofs.
- **Proofs** (19:37 to 2026-11-25, 04:19): twelve proof agents, each in a worktree of its own, on a group of files in
  dependency order: the graph basics of Sections 2–3; Proposition 1 and Lemma 17; the cited results of Allman, Degnan
  and Rhodes 2011; Section 5, in two agents; Sections 6–7; Sections 8–9; the examples; the Solution's bridges and the
  Challenge's checks; the correspondences of cycles and the figures; Proposition 5; Lemma 17's case 4 (ii). The agents
  of Sections 8–9 and of Proposition 5 ran 28 sub-agents of their own on parts of their proofs. The main session
  integrated their branches, ran the audit and the route check, and sent agents back whenever a review found a step
  that did not follow the paper or a departure without a reason the procedure admits.
- **Verification and cleanup**: the axiom audit and the route check after every merge; a cleanup agent (03:43–04:51)
  for the warnings, the unused hypotheses, duplicated helpers and the general lemmas of [`Banos2019/Basic/`](../../Banos2019/Basic). On
  [`scripts/check_kernels.sh`](../../scripts/check_kernels.sh) (04:55), Lean's kernel and NanoDa, through Comparator, accept the eleven theorems of the
  Challenge, and con-ron accepts them, in an export of 50,734 declarations.
- **Documents** (03:57 to the end): this file, the report and the README by one agent, with a sub-agent that checked
  the literature section's claims against their sources.

The same session also coordinated work on other repositories of the collection, which the main session's figures
below include and the sub-agents' figures do not: the move of the collection to new releases of its libraries, the
reorganization of the hubs, and the arrangement of eight paper repositories in the collection's layout (eleven
sub-agents). The machine restarted at about 21:30; the agents then running resumed at 22:15 with their work intact.

Figures, from the start, 2026-11-24 18:29:23, to the end of the round, the commit 95f7ca2 of 2026-11-25 05:44, from the
transcripts (`session_stats.py` of the skill):

- elapsed time: 11.25 h;
- sub-agents on this paper: 54 (23 launched by the main session, 31 by those), at most 8 running
  at once, 42.2 h of working time in all;
- their work: 5,583 tool calls; 10.87M output tokens, 41.12M input tokens, 1,866M tokens read from the cache;
- the main session: 548 tool calls; 0.71M output tokens, 1.46M input tokens, 272M tokens read from the cache;
- model calls: `claude-opus-5-5` only, 578 by the main session and 5420 by the sub-agents on this paper.

The sub-agents of the other repositories add 11 agents, 10.9 h of working time, 3,183 tool calls, and
2.90M output tokens, 9.48M input tokens, 1,360M tokens read from the cache. The platform does not record spending. The figures leave out the time the maintainer spent reading
and deciding between requests.
