# Roadmap

This document outlines potential improvements, new features, and code cleanup opportunities for the Convergent CRDT library.

## Completed

The following roadmap items have been implemented:

| Item | Description |
|------|-------------|
| ✓ ORMap | Observed-remove map with nested CRDT support |
| ✓ TwoPGraph | Two-phase graph (vertices and edges are TwoPSets) |
| ✓ EWFlag/DWFlag | Enable-wins and disable-wins flag CRDTs |
| ✓ LWWElementSet | Per-element timestamp set |
| ✓ PNMap | Map with PNCounter values |
| ✓ LSEQ | Adaptive position-based sequence CRDT |
| ✓ Fugue | Tree-based text CRDT with maximal non-interleaving |
| ✓ Property-Based Tests | 168 tests covering all CRDT laws with Plausible |
| ✓ Merge Tests | Covered by property tests (commutativity, associativity, idempotency) |
| ✓ Binary Serialization | LEB128/ZigZag encoding for all 19 CRDT types with round-trip tests |
| ✓ CmRDTQuery Instances | All CRDTs now have CmRDTQuery instances for consistent querying |
| ✓ Monadic Interface | StateM-based CRDTM monad with runCRDT and per-CRDT helpers (incM, addM, etc.) |

---

## Feature Proposals

### [Priority: High] Add Delta-state CRDTs (delta-CRDTs)

**Description:** Implement delta-state CRDTs that transmit only the state changes (deltas) rather than full operations or full state. This provides a middle ground between state-based and operation-based CRDTs with better bandwidth efficiency.

**Rationale:** Delta-state CRDTs offer significant bandwidth savings over traditional state-based CRDTs while being more flexible than pure operation-based CRDTs. They are particularly valuable for mobile/IoT scenarios with limited bandwidth.

**Affected Files:**
- New file: `Convergent/Core/Delta.lean` (delta typeclass)
- New file: `Convergent/Counter/DeltaGCounter.lean`
- New file: `Convergent/Set/DeltaORSet.lean`
- Updates to existing CRDTs to add delta extraction

**Estimated Effort:** Large

**Dependencies:** None

---

### [Priority: Medium] Add JSON Serialization

**Description:** Add JSON serialization for all CRDT types to complement the existing binary serialization.

**Rationale:** JSON is human-readable and widely used for debugging, APIs, and interoperability with other systems. Binary serialization is already complete for efficient network transmission.

**Affected Files:**
- New file: `Convergent/Serialization/Json.lean`
- Update `Convergent/Serialization.lean` to export JSON module

**Estimated Effort:** Medium

**Dependencies:** May require a JSON library dependency

**Note:** Binary serialization is complete in `Convergent/Serialization/Binary.lean` with LEB128 variable-length encoding for Nat, ZigZag encoding for Int, and instances for all 19 CRDT types.

---

### [Priority: Medium] Add Causal Delivery Helper

**Description:** Implement a causal delivery layer that buffers out-of-order operations and delivers them in causal order.

**Rationale:** The current library assumes the application handles causal delivery. A built-in causal delivery layer would make it easier to build correct distributed systems.

**Affected Files:**
- New file: `Convergent/Delivery/CausalBuffer.lean`
- New file: `Convergent/Delivery/ReliableBroadcast.lean`

**Estimated Effort:** Large

**Dependencies:** Requires VectorClock (already present)

---

### [Priority: Medium] Add Increment-by-N for Counters

**Description:** Extend GCounter and PNCounter to support incrementing/decrementing by arbitrary positive values, not just 1.

**Rationale:** Many use cases require adding or subtracting values other than 1 (e.g., adding 5 items to a cart). Currently this requires multiple increment operations.

**Affected Files:**
- `Convergent/Counter/GCounter.lean` (lines 23-28, 42-48)
- `Convergent/Counter/PNCounter.lean` (lines 24-28, 41-54)

**Estimated Effort:** Small

**Dependencies:** None

---

### [Priority: Low] Add JSON CRDT

**Description:** Implement a JSON CRDT that supports nested documents with automatic conflict resolution at each level.

**Rationale:** JSON is ubiquitous for data interchange. A JSON CRDT would enable building collaborative document editing applications.

**Affected Files:**
- New file: `Convergent/Document/JsonCRDT.lean`
- Update `Convergent.lean` to export the new module

**Estimated Effort:** Large

**Dependencies:** ORMap (✓ implemented), LWWRegister (✓ implemented)

---

## Code Improvements

### [Priority: High] Use HashSet Instead of List in GSet

**Current State:** `GSet` uses `List α` to store elements (line 15 of `GSet.lean`), requiring O(n) containment checks and O(n) duplicate detection on add.

**Proposed Change:** Use `Std.HashSet` for O(1) average containment checks and insertion.

**Benefits:** Significant performance improvement for sets with many elements.

**Affected Files:**
- `Convergent/Set/GSet.lean` (lines 14-17, 32-34, 43-46, 52-56)
- `Convergent/Set/TwoPSet.lean` (depends on GSet)

**Estimated Effort:** Small

---

### [Priority: High] Add Hashable Constraint Consistently

**Current State:** `ORSet` requires `[Hashable α]` but `GSet` and `TwoPSet` only require `[BEq α]`, leading to inconsistent performance characteristics and constraints.

**Proposed Change:** Either make all sets use HashMap/HashSet (requiring Hashable), or provide both variants.

**Benefits:** Consistent performance and API across set types.

**Affected Files:**
- `Convergent/Set/GSet.lean`
- `Convergent/Set/TwoPSet.lean`

**Estimated Effort:** Small

---

### [Priority: High] Optimize RGA Operations

**Current State:** RGA `insertAfter` uses list traversal (O(n)) and `merge` creates intermediate lists and uses qsort. The `findIndex` function at line 49 scans the list.

**Proposed Change:** Use a more efficient data structure such as a balanced tree or skip list for maintaining the sequence. Consider using a rope-like structure for large documents.

**Benefits:** Better performance for long sequences, essential for text editing use cases.

**Affected Files:**
- `Convergent/Sequence/RGA.lean` (lines 49, 76-106, 133-149)

**Estimated Effort:** Large

---

### [Priority: Medium] Extract Common Decidable Boilerplate

**Current State:** `LamportTs`, `UniqueId`, and other types have nearly identical boilerplate for `Decidable (a < b)` and `Decidable (a <= b)` instances (see lines 52-62 in `Timestamp.lean`, lines 43-53 in `UniqueId.lean`).

**Proposed Change:** Create a helper function or derive macro to generate these instances from the `Ord` instance.

**Benefits:** Reduced code duplication, easier maintenance.

**Affected Files:**
- `Convergent/Core/Timestamp.lean` (lines 52-62)
- `Convergent/Core/UniqueId.lean` (lines 43-53)
- Potentially create new file: `Convergent/Core/Ordering.lean`

**Estimated Effort:** Small

---

### [Priority: Medium] Add Efficient Bulk Operations

**Current State:** `CmRDT.applyMany` applies operations one at a time via `foldl` (line 33-34 of `CmRDT.lean`).

**Proposed Change:** Add specialized bulk operation methods to each CRDT that can batch operations more efficiently (e.g., bulk insert for sets, bulk increment for counters).

**Benefits:** Better performance for high-throughput scenarios.

**Affected Files:**
- `Convergent/Core/CmRDT.lean`
- All CRDT implementation files

**Estimated Effort:** Medium

---

### [Priority: Medium] Add Configurable Tie-Breaking Strategy

**Current State:** Timestamp ties are always broken by replica ID (higher replica wins). This is hardcoded in `LamportTs.compare` (line 39).

**Proposed Change:** Make tie-breaking configurable (e.g., add-wins vs remove-wins, higher vs lower replica ID).

**Benefits:** More flexible conflict resolution policies.

**Affected Files:**
- `Convergent/Core/Timestamp.lean` (lines 36-41)
- All CRDTs using LamportTs

**Estimated Effort:** Medium

**Dependencies:** May require type-level configuration or runtime options

---

### [Priority: Low] Add Operation Logging/Audit Trail

**Current State:** Operations are applied directly with no history.

**Proposed Change:** Add an optional wrapper that maintains an operation log for debugging, auditing, or replay.

**Benefits:** Better debugging, ability to replay history, audit compliance.

**Affected Files:**
- New file: `Convergent/Debug/OpLog.lean`

**Estimated Effort:** Medium

---

### [Priority: Low] Add Pruning/Garbage Collection for Tombstones

**Current State:** RGA and ORSet accumulate tombstones forever. In RGA, deleted nodes remain in the list with `value := none` (line 120-122). In ORSet, erased elements are removed from the map but tags accumulate.

**Proposed Change:** Add garbage collection mechanisms that can safely prune tombstones when all replicas have observed the deletion.

**Benefits:** Reduced memory usage for long-running systems.

**Affected Files:**
- `Convergent/Sequence/RGA.lean`
- `Convergent/Set/ORSet.lean`
- New file: `Convergent/GC/TombstoneGC.lean`

**Estimated Effort:** Large

**Dependencies:** Requires tracking of replica state (causal stability)

---

## Code Cleanup

### [Priority: High] Add Comprehensive Documentation

**Issue:** While top-level module comments exist, many functions lack documentation. The library would benefit from more examples and explanation of edge cases.

**Location:**
- All CRDT files lack detailed function-level documentation
- No doc comments on private helper functions

**Partial Progress:**
- ✓ Added `ScenarioTests.lean` with 46 real-world usage examples covering all 17 CRDTs:
  - Shopping cart (ORSet), Like button (GCounter), User presence (EWFlag)
  - Leaderboard (LWWMap), Social network (TwoPGraph), Inventory (PNMap)
  - Collaborative text editing (Fugue), Conflict resolution (MVRegister)
  - Feature flags (LWWElementSet), Document viewers (GSet)
  - Redeemable coupons (TwoPSet), User profile (LWWRegister)
  - Per-channel message counts (ORMap), Task list (RGA)
  - Priority queue (LSEQ), Emergency stop (DWFlag)

**Action Required:**
1. Add doc comments to all public functions explaining parameters and behavior
2. ~~Add examples in doc comments~~ (scenario tests serve as examples)
3. Document edge cases and concurrent operation semantics

**Estimated Effort:** Medium

---

### [Priority: Medium] Standardize Constructor Naming

**Issue:** Inconsistent constructor naming across modules:
- `UniqueId.new` vs `UniqueId.mk` (README uses `.mk` but code has `.new`)
- `LamportTs.new` vs `LamportTs.mk` (README uses `.mk` but code has `.new`)

**Location:**
- `Convergent/Core/UniqueId.lean` (line 24: uses `new`)
- `Convergent/Core/Timestamp.lean` (line 23: uses `new`)
- `README.md` (lines 62, 69, 89: uses `mk`)

**Action Required:** Either update code to use `.mk` or update README to use `.new` for consistency.

**Estimated Effort:** Small

---

### [Priority: Low] Remove Unused Imports

**Issue:** Some files may have unused imports (e.g., `Std.Data.HashMap` in files that might not use it).

**Location:** All source files

**Action Required:** Audit imports and remove any that are unused.

**Estimated Effort:** Small

---

### [Priority: Low] Add Benchmarks

**Issue:** No performance benchmarks exist to track performance over time.

**Location:** Would be new files

**Action Required:**
1. Create `ConvergentBench/` directory
2. Add benchmarks for each CRDT type
3. Include benchmarks for:
   - Single operations
   - Bulk operations
   - Merge operations
   - Large state handling

**Estimated Effort:** Medium

---

### [Priority: Low] Improve Error Messages

**Issue:** The library uses `Option` types for missing values but no error messages explain why operations might fail or return `none`.

**Location:** All CRDT query functions returning `Option`

**Action Required:** Consider adding `Except` variants for operations that need detailed error information, or add documentation explaining when `none` is returned.

**Estimated Effort:** Small

---

## Architectural Considerations

### Consider Adding a Typeclass Hierarchy

The current `CmRDT` and `CmRDTQuery` typeclasses could be expanded into a richer hierarchy:
- `Semilattice` - for merge operations
- `CvRDT` - state-based CRDTs
- `CmRDT` - operation-based CRDTs
- `DeltaCRDT` - delta-state CRDTs

This would enable more generic algorithms and better code reuse.

### Consider Separating State and Operations

Currently each CRDT defines both its state type and operation type. Consider using a more generic approach where operations are defined separately and can be composed.

### Consider Adding Middleware/Interceptor Pattern

For cross-cutting concerns like logging, metrics, and validation, a middleware pattern could wrap CRDT operations without modifying the core types.
