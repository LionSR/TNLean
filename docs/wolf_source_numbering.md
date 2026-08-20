# Numbering in the local Wolf transcription

The files in `Notes/WolfNoteTexSource/` are a useful searchable transcription
of M. Wolf, *Quantum Channels & Operations: Guided Tour*.  Their automatically
rendered theorem numbers are not, in general, the theorem numbers of the
published notes.

The shared declarations in `preamble.tex` use one theorem counter, reset by
section.  In particular, `ch06_spectral_properties.tex` has been transcribed as
one section, whereas the published chapter has several sections.  Lemmas,
propositions, corollaries, examples, problems, and remarks therefore contribute
to one unbroken local counter.  The two numberings agree near the beginning of
the chapter and diverge later.

Wolf's own cross-references in the chapter are the primary local evidence for
the published numbering.  For example, the proof of *Unique fixed points of
full rank* and the proof of *Asymptotic image* both cite Corollary 6.5 for the
result *Linearly independent stationary states*.  The local counter renders
that result as 6.29; neither the local rendering nor the formerly used number
6.8 is the published citation.

When adding a source reference, use the following order of evidence:

1. Wolf's explicit cross-reference in the text;
2. the number in the published notes;
3. if neither is available, the result's title and a line range in the local
   source, without an inferred theorem number.

The same caution applies to every chapter whose local section structure differs
from the published notes.  A number should not be inferred solely from a local
rendering.
