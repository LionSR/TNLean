# Numbering in the local Wolf transcription

> **Where the transcription lives.** The transcription and the archived
> chapter PDFs moved to the companion
> [QICLean](https://github.com/LionSR/QICLean) repository in the
> quantum-channel extraction: they are `Notes/WolfNoteTexSource/` and
> `Notes/WolfNotePDF/` *in QICLean*, not in this repository. Every
> `Notes/WolfNoteTexSource/...` path in this document refers to that directory;
> checking such a citation requires a QICLean checkout.

The files in `Notes/WolfNoteTexSource/` are a useful searchable transcription
of M. Wolf, *Quantum Channels & Operations: Guided Tour*.  Their automatically
rendered theorem numbers are not, in general, the theorem numbers of the
published notes.

The shared declarations in `Notes/WolfNoteTexSource/preamble.tex` use one
theorem counter, reset by section.  Chapter 6 overrides those declarations:
`ch06_spectral_properties.tex` undefines the shared environments and gives
propositions, corollaries, lemmas, definitions, examples, and remarks separate
section-scoped counters.  Since that file is one section numbered 6, its fifth
corollary is rendered as Corollary 6.5.  Equation numbers have an independent
counter; in particular, 6.29 is an equation number, not the local number of
this corollary.

Wolf's own cross-references in the chapter are the primary local evidence for
the published numbering.  For example, the proof of *Unique fixed points of
full rank* and the proof of *Asymptotic image* both cite Corollary 6.5 for the
result *Linearly independent stationary states*.  The local corollary counter
also renders that result as 6.5; the formerly used number 6.8 is not the
published citation.

When adding a source reference, use the following order of evidence:

1. Wolf's explicit cross-reference in the text;
2. the number in the published notes;
3. if neither is available, the result's title and a line range in the local
   source, without an inferred theorem number.

The same caution applies to every chapter whose local section structure differs
from the published notes.  A number should not be inferred solely from a local
rendering.
