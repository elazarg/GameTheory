# Assumption Audit Template (Per Theorem)

Use this template for any theorem in game-theory modules.

## Theorem

- file:
- declaration:
- family (`F1..F7`):

## Goal Shape (definition-free)

Write in one line as implication/equality over existing primitives.

## Current Assumptions

List all typeclass + predicate assumptions from statement.

## Usage Classification

- `E` essential
- `?` maybe removable
- `A` adapter-only (format-specific)

## Dependency Breakdown

- `L0` function/list algebra:
- `L1` probability algebra:
- `L2` sequential semantics:
- `L3` adapters:

## Cross-Field Alias

Closest known theorem shape/name from another field.

## Proposed Minimal Statement

Rewrite with only `E` + required interfaces.

## Validation Plan

1. identify one call site
2. replace old lemma with proposed shape
3. note additional adapter obligations

