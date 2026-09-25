# Blueprint for the DeGiorgi formalization

This adds a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
blueprint generated from `DeGiorgi_Lean_to_Tex.tex` and the Lean sources.

## What was generated

- 348 blueprint nodes (77 definitions, 271 theorem/lemma/proposition/corollary)
  in 8 chapters, one per section of the companion document.
- Every node carries `\leanok`; 337 nodes carry `\lean{...}` (487 Lean names in total).
- 246 missing `\label`s were added (`thm:`, `lem:`, `def:`, ... prefixes).
- 1,608 `\uses{...}` edges were computed from the Lean code: for each tagged
  declaration, the references in its statement (for `\uses` on the statement) and in
  its proof (for `\uses` on the proof) were followed through untagged helper lemmas
  until they reached another blueprint node. Existing `\ref{}`s inside proofs were
  added as well. The resulting graph is acyclic.
- 23 statements that had no proof in the companion got a stub proof block
  ("See the Lean formalization.") so they show as proved in the dependency graph.
- Display math `\[ ... \]` was converted to `equation*`.
- 13 nodes point to `private` declarations. Private names cannot be checked by
  `checkdecls` or linked to doc-gen4, so they are listed in the statement text
  instead of in `\lean{}`.

## Layout

    blueprint/src/            blueprint sources (content.tex, chapters/, macros/, print.tex, web.tex)
    blueprint/scripts/        conversion scripts + conversion_report.json
    .github/workflows/blueprint.yml
    lakefile.lean             adds the `checkdecls` dependency

## Building locally

    pip install leanblueprint
    lake update checkdecls        # adds checkdecls to lake-manifest.json
    lake build
    leanblueprint pdf             # blueprint/print/print.pdf
    leanblueprint web             # blueprint/web/
    leanblueprint checkdecls      # checks all \lean{} names exist
    leanblueprint serve           # preview at http://localhost:8000

In the GitHub repository settings, set Pages -> Source to "GitHub Actions".

## Regenerating

`blueprint/scripts/regenerate.sh` rebuilds `blueprint/src` from scratch (it
overwrites manual edits). Once you start editing the blueprint by hand, stop
regenerating and treat `blueprint/src` as the source of truth.

## Known limitations

- Name resolution and dependency extraction are textual (a Python parser of the
  `.lean` files), not elaborated. All header names resolved, but `checkdecls`
  in CI is the real test. Dot-notation calls (`h.foo`) are matched only when the
  final name component is unique in the project, so a few edges may be missing
  or spurious.
- Proof `\uses` go through untagged helper lemmas and noncomputable constants, so
  some proofs list many definition nodes (e.g. constants like `C_Moser`).
- The informal text itself is unchanged from the machine-generated companion and
  has not been checked against the Lean statements.
