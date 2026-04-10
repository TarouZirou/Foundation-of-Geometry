# Foundation of Geometry (Lean 4)

This repository formalizes a Hilbert-style axiomatic foundation of geometry in Lean 4.

## Current contents

- `Hilbert/Basic.lean`
  - Core structure `Geometry` (points, lines, planes, incidence, betweenness, congruence).
  - Incidence axioms (`IncidentAxioms`) and derived theorems.
  - Order axioms (`OrderAxioms`) and derived theorems.
- `Hilbert.lean`
  - Top-level entry point importing `Hilbert.Basic`.

## Build

This project uses Lake. After installing Lean 4 and Lake:

```bash
lake build
```

## Goal

The long-term goal is a mechanically checked development of foundational Euclidean geometry from explicit axioms, with theorems proved directly from those axioms.
