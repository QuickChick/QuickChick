# Derivation command migration

The public dispatcher has not switched engines yet. Scheduled derivations now
register instances, and tactic-generated helpers are local proof definitions.
The next change must preserve the following command contracts.

| Entry point | Current behavior | Migration requirement |
| --- | --- | --- |
| `quickchick` | Scheduled engine; proof-local helpers and saved tests | Preserve flags, schedule selection, and execution defaults |
| `Derive Inductive Schedule` | Scheduled engine; persistent declarations | Keep explicit mode/output selection and collision errors |
| `QCDerive GenSized` | Simple engine; accepts `Gen A` for parameter `A` | Adapt the scheduled engine's `GenSized A` prerequisites without requiring new dictionaries from existing callers |
| `QCDerive EnumSized` | Simple engine; accepts `Enum A` | Preserve that contract while adapting `EnumSized A` prerequisites |
| `QCDerive Arbitrary` | Derives generator and shrinker | Route generation through the new engine and retain shrinking |
| `QCDerive DecOpt` / `Checker` | Dependent engine; predicate application syntax | Elaborate type arguments and preserve input ordering and default instance names |
| `QCDerive GenSizedSuchThat` / `ArbitrarySizedSuchThat` / `Generator` | Dependent engine; output selected by a lambda | Preserve typed/implicit arguments, tuple outputs, and supplied input variables |
| `QCDerive EnumSizedSuchThat` / `Enumerator` | Dependent engine; lambda-selected outputs | Preserve the corresponding enumeration contracts |
| `QCDerive Show`, `Shrink`, `Sized` | Simple engine | Retain these implementations |
| Bare `Derive` after importing `LegacyDerive` | Alias of the public dispatcher | Follow the new dispatcher; this import does not select an old engine |
| Proposed `QCDeriveLegacy` / `DeriveLegacy` | Not implemented | Explicit deprecated access to old algorithms; no silent fallback |

`test/derivation_contracts.v` checks Gen-only and Enum-only callers, default
instance names, aliases, and repeated explicit derivations. `rebase_compat.v`
checks mutual blocks and the `using` forms. The current public command gives
repeated derivations fresh names; the schedule command reports a collision.
These differences need an adapter rather than a direct dispatcher substitution.

The syntax adapter must identify output positions after elaborating implicit
type arguments. Counting written arguments is insufficient. Keep compatibility
aliases for existing generated names where their types remain compatible, and
record any necessary signature change explicitly before switching dispatch.
Do not add a global reverse `Gen -> GenSized` instance alongside `GenOfGenSized`:
that would introduce a typeclass search cycle. Use scoped adapters or wrapper
construction at the public derivation boundary.
