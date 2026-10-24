# Instructions for AI agents working in this bundle

Start with [the topic guide](topics/classicism/AGENTS.md) for terminology, record IDs, and construction-specific entry points. Run commands from this bundle's root. Read `topic.yaml`, the relevant section of `background.md`, and the matching principle records under `topics/classicism/`; then follow their IDs into `results/`, `models/`, and `writeups/`. Search narrowly before reading whole files.

Translate the user's question into exact premises and a target, preserving the fixed framework and distinguishing optional presets. Inspect definitions, proofs, model constructions, status, and source caveats. For derived evidence, use `scripts.pmap.load_topic` and `Engine` with proved-only records: `entails`, `excludes`, and `separates` answer different questions. Keep optional assumptions in the queried premise set, not the engine background, so a countermodel must actually satisfy them.

`MAP.md`, `derived.json`, and `OPEN-QUESTIONS.md` are searchable references; do not read the entire database or compute all rankings for one question. Unknown in the records does not mean false or open in the literature. Once the local evidence is identified, work on the mathematics; distinguish a new argument from recorded evidence. A mathematical question alone does not request record edits or a rebuild. `README.md` supplies the full semantics and record formats.

Mathematical brainstorming and Lean formalization are separate tasks. Default to ordinary mathematical arguments. Requests to prove or check a claim do not by themselves request Lean. Unless Lean work is explicitly requested or already agreed, do not explore Lean sources, edit `.lean` files, install toolchains, run `lake`, or run `lean-check`. A sound mathematical proof need not be formalized to answer or record it; preserve the actual Lean status. Routine export builds may mechanically regenerate statements without starting a proof or audit task. Do not routinely offer formalization as the next step in brainstorming.

## Always

- Run `python3 scripts/pmap.py validate` after every batch of edits. It must pass.
- After changing the engine or viewer, run `python3 scripts/pmap.py selftest` and `python3 scripts/check_falsity.py` (requires Node).
- Give every new result and model a nonempty `sources` with theorem/section and page, and set `certificate.source_id` to the direct source: `bacon-dorr-classicism`, `dorr-bc-not-rc`, `lewin-1991`, `prior-1963`, `prior-lemmon`, `bacon-2020`, `bacon-2024-book`, `bacon-mathematical-contingency`, `barton-goodsell-continuum-contingency`, `the-broadest-necessity`, `necessity-of-identity`, `goodsell-yli-vakkuri-unpublished`, `goodsell-pc`, `goodsell-arithmetic-necessary`, `sun-possible-worlds-without-atomicity`, `bounds-of-possibility`, `misc`.
- Record independence as a **model**, never as a result.
- Name models by their construction or ordering rule: family first, then the rule and any distinguishing variant. Match the write-up title. Keep authorship, conjecture status, and lists of satisfied/violated principles in their own fields. For conjectured extensions, do not invent an unknown construction. Keep existing record IDs unchanged.
- List in a model's `satisfies` and `violates` only what you actually verified. The engine derives the rest and reports what stays unknown.
- Log every later addition to an existing record in its `changes` list (date, by, summary, and for models the newly verified `satisfies`/`violates` ids). Never move `certificate.date`.
- A model written as a `definition` and `arguments` takes a new verdict as a new argument with its own `by` and `date`, and a correction in that argument's `revisions`. Its `history` is frozen, and its `satisfies`/`violates` are computed: never write them. It records only the verdicts the engine cannot derive from the others, its source's first.
- Write the real proof in `proof`, at referee detail. Put anything longer than a paragraph in `topics/classicism/writeups/<id>.md` instead.
- Prefer `status: conjectured` with an empty proof and a note saying what would settle it, over a `proved` you are not certain of.

## Never

- Never invent an author, date, page, DOI or submission label. Unsure means say so in `notes`.
- Never cite a paper as `source_id` for a proof you produced yourself. That is `misc`.
- Never put anything in `checked_by` unless a named person actually checked it.
- Never change the mathematical content of an existing published or human-authored proof. Add a note or a new record.
- Never rename an `id` that other files reference. File name equals id.
- Record incompatible premises with `conclusion: false`, not a duplicate failure principle. Never use false as a principle, premise, model assertion, or background assumption.
- Never treat a missing arrow as a proof of non-implication. Missing means not recorded.
- Never use a conjecture as evidence for anything.
- Never edit `Statements.lean`; it is generated from the records by `pmap lean`.
- Never set `lean: verified` by hand. Only `pmap lean-check` may conclude that, and only
for a proof that inhabits the generated statement without `sorryAx`.

## Reading the derived state

`MAP.md` §6 and `derived.json` are computed from the proved records by closure. Do not hand-edit them; they regenerate. If a verdict looks wrong, the fix is in the YAML.

