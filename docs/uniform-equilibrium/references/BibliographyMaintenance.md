# Bibliography maintenance queue

This is a citation-maintenance queue, not a mathematical priority list. The
Markdown bibliography is substantially richer than `latex/references.bib` and
the manuscript bibliography. Reconcile them without changing theorem status.

## Missing or incomplete entries

- Vieille 2000 III, Vrieze--Thuijsman 1989, Flesch--Thuijsman--Vrieze 1996
  and 1997, Kohlberg 1974, Bewley--Kohlberg's recursion-equation paper,
  Solan--Vohra 2002, Simon 2012, Hansen--Ibsen-Jensen--Neyman 2023, Everett
  1957, Gillette 1957, and Solan's 2022 textbook.
- Add the distinct Solan--Vieille 2002 *Quitting Games--An Example* citation;
  do not merge it with the 2001 MOR *Quitting Games* paper or the 2002 GEB
  correlated-equilibrium paper.

## Known metadata traps

- Bewley--Kohlberg's two 1976 MOR papers have different issues/pages/DOIs.
- Renault's JEMS DOI ends in `/254`, not `/256`.
- Vieille's two-player solution spans Parts I and II; Part III is auxiliary,
  and Vieille is sole author.
- Sorin's uniform payoff set includes the bounds `1/2 <= a <= 2/3`.
- Keep correlated-device notions distinct in titles and annotations.

Acceptance: every cited theorem in
[`UniformEquilibriumLiterature`](../../../ideas/UniformEquilibriumLiterature/README.md)
has one canonical bibliography entry, and manuscript references compile with
no duplicate-key or unresolved-citation warning.
