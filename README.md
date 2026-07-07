# Automated Planning in Lean 4

This repository contains a Lean 4 library implementing the STRIPS formalism for automated planning.

The source documentation can be found at <https://amosnico.github.io/lean4-strips/docs/Strips/PlanningTask.html>

## Goals

This project originated as part of a [certificate validator for automated planning](https://github.com/AmosNico/validator). The goal is to expand it into a general-purpose library useful for anyone working on automated planning in Lean 4.

The library aims to be both easy to work with for formalizing theoretical results about the automated planning, and efficient at runtime.

## Usage

Add the following dependency to your `lakefile.toml`:
```toml
[[require]]
name = "strips"
git = "https://github.com/AmosNico/lean4-strips"
rev = "main"
```

Then add `import Strips` at the top of any Lean file where you want to use the library.
