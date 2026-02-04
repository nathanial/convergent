/-
  Scenario-Based Tests for Convergent

  These tests demonstrate real-world usage patterns for CRDTs.
  Each scenario tells a story that serves as both documentation and verification.
-/
import Convergent
import Crucible

namespace ConvergentTests.ScenarioTests

open Crucible
open Convergent

/-! ## Shopping Cart with ORSet

A common e-commerce scenario: multiple devices modifying a shopping cart.
ORSet allows adding and removing items with support for re-adding after removal.
-/

testSuite "Shopping Cart (ORSet)"

test "add items from phone and laptop, sync later" := do
  -- User's phone and laptop each have a replica
  let phone : ReplicaId := 1
  let laptop : ReplicaId := 2

  -- Phone adds milk and bread
  let phoneTag1 := UniqueId.new phone 0
  let phoneTag2 := UniqueId.new phone 1
  let phoneCart := ORSet.empty
    |> fun s => ORSet.apply s (ORSet.add "milk" phoneTag1)
    |> fun s => ORSet.apply s (ORSet.add "bread" phoneTag2)

  -- Laptop adds eggs and butter (concurrently, offline)
  let laptopTag1 := UniqueId.new laptop 0
  let laptopTag2 := UniqueId.new laptop 1
  let laptopCart := ORSet.empty
    |> fun s => ORSet.apply s (ORSet.add "eggs" laptopTag1)
    |> fun s => ORSet.apply s (ORSet.add "butter" laptopTag2)

  -- Later, devices sync - merge combines all items
  let syncedCart := ORSet.merge phoneCart laptopCart

  (syncedCart.contains "milk") ≡ true
  (syncedCart.contains "bread") ≡ true
  (syncedCart.contains "eggs") ≡ true
  (syncedCart.contains "butter") ≡ true
  (syncedCart.size) ≡ 4

test "remove item on one device, add on another concurrently" := do
  -- Both devices start with milk in cart
  let phone : ReplicaId := 1
  let laptop : ReplicaId := 2
  let initialTag := UniqueId.new phone 0

  let initialCart := ORSet.apply ORSet.empty (ORSet.add "milk" initialTag)

  -- Phone removes milk
  let phoneRemoveOp := ORSet.remove initialCart "milk"
  let phoneCart := ORSet.apply initialCart phoneRemoveOp

  -- Laptop adds milk again (concurrent, doesn't know about removal)
  let laptopTag := UniqueId.new laptop 0
  let laptopCart := ORSet.apply initialCart (ORSet.add "milk" laptopTag)

  -- Sync: Add wins! The laptop's add has a fresh tag not seen by remove
  let syncedCart := ORSet.merge phoneCart laptopCart

  (syncedCart.contains "milk") ≡ true

test "checkout then continue shopping" := do
  -- After checkout, start fresh but can re-add same items
  let user : ReplicaId := 1
  let tag1 := UniqueId.new user 0
  let tag2 := UniqueId.new user 1

  -- Add apple, then remove it (checkout)
  let cart := ORSet.apply ORSet.empty (ORSet.add "apple" tag1)
  let removeOp := ORSet.remove cart "apple"
  let emptyCart := ORSet.apply cart removeOp

  (emptyCart.contains "apple") ≡ false

  -- Later, add apple again for a new order
  let newCart := ORSet.apply emptyCart (ORSet.add "apple" tag2)

  (newCart.contains "apple") ≡ true

/-! ## Like Button with GCounter

A social media like button that works across multiple servers.
GCounter is grow-only, perfect for counting events that can't be undone.
-/

testSuite "Like Button (GCounter)"

test "likes from different server regions aggregate correctly" := do
  -- Each region has its own server
  let usEast : ReplicaId := 1
  let usWest : ReplicaId := 2
  let europe : ReplicaId := 3

  -- US-East receives 3 likes
  let usEastCounter := GCounter.empty
    |> fun s => GCounter.apply s (GCounter.increment usEast)
    |> fun s => GCounter.apply s (GCounter.increment usEast)
    |> fun s => GCounter.apply s (GCounter.increment usEast)

  -- US-West receives 2 likes
  let usWestCounter := GCounter.empty
    |> fun s => GCounter.apply s (GCounter.increment usWest)
    |> fun s => GCounter.apply s (GCounter.increment usWest)

  -- Europe receives 5 likes
  let europeCounter := GCounter.empty
    |> fun s => GCounter.apply s (GCounter.increment europe)
    |> fun s => GCounter.apply s (GCounter.increment europe)
    |> fun s => GCounter.apply s (GCounter.increment europe)
    |> fun s => GCounter.apply s (GCounter.increment europe)
    |> fun s => GCounter.apply s (GCounter.increment europe)

  -- Global sync: merge all regions
  let global := GCounter.merge usEastCounter usWestCounter
    |> fun s => GCounter.merge s europeCounter

  (global.value) ≡ 10
  (global.getCount usEast) ≡ 3
  (global.getCount usWest) ≡ 2
  (global.getCount europe) ≡ 5

test "duplicate operations don't double count" := do
  let server1 : ReplicaId := 1
  let server2 : ReplicaId := 2

  -- Server 1 counts 2 likes
  let s1 := GCounter.empty
    |> fun s => GCounter.apply s (GCounter.increment server1)
    |> fun s => GCounter.apply s (GCounter.increment server1)

  -- Server 2 also processes server 1's operations (duplicates) plus its own
  let s2 := GCounter.empty
    |> fun s => GCounter.apply s (GCounter.increment server1)  -- duplicate
    |> fun s => GCounter.apply s (GCounter.increment server1)  -- duplicate
    |> fun s => GCounter.apply s (GCounter.increment server2)

  -- Merge takes max per replica, not sum - no double counting
  let merged := GCounter.merge s1 s2

  (merged.value) ≡ 3  -- 2 from server1 + 1 from server2

/-! ## User Presence with EWFlag

Track if a user is online across multiple devices.
EWFlag (enable-wins) ensures that if any device is online, user shows online.
Note: EWFlag is timestamp-based - concurrent enable/disable resolves to enabled,
but a later disable can turn the flag off.
-/

testSuite "User Presence (EWFlag)"

test "user online on phone, offline on laptop - shows online" := do
  let phone : ReplicaId := 1
  let laptop : ReplicaId := 2

  -- Phone enables (user active)
  let phoneTs := LamportTs.new 1 phone
  let phoneStatus := EWFlag.apply EWFlag.empty (EWFlag.enable phoneTs)

  -- Laptop disables (user closed app, concurrent)
  let laptopTs := LamportTs.new 1 laptop
  let laptopStatus := EWFlag.apply EWFlag.empty (EWFlag.disable laptopTs)

  -- Merge: enable wins - user is online
  let merged := EWFlag.merge phoneStatus laptopStatus

  (merged.value) ≡ true

test "EWFlag later disable turns off" := do
  let phone : ReplicaId := 1
  let laptop : ReplicaId := 2

  -- Phone enables at time 1
  let online := EWFlag.apply EWFlag.empty (EWFlag.enable (LamportTs.new 1 phone))

  -- Later disable at time 2 wins (not concurrent)
  let withDisable := EWFlag.apply online (EWFlag.disable (LamportTs.new 2 phone))
  let withLaptopDisable := EWFlag.apply withDisable (EWFlag.disable (LamportTs.new 3 laptop))

  (withLaptopDisable.value) ≡ false

/-! ## Leaderboard with LWWMap

A game leaderboard where player scores are updated concurrently.
LWWMap uses timestamps to resolve conflicts - most recent score wins.
-/

testSuite "Leaderboard (LWWMap)"

test "concurrent score updates resolved by timestamp" := do
  let server1 : ReplicaId := 1
  let server2 : ReplicaId := 2

  -- Server 1 records Alice's score of 100 at time 1
  let ts1 := LamportTs.new 1 server1
  let board1 := LWWMap.apply LWWMap.empty (LWWMap.put "Alice" 100 ts1)

  -- Server 2 records Alice's score of 150 at time 2 (later, she scored more)
  let ts2 := LamportTs.new 2 server2
  let board2 := LWWMap.apply LWWMap.empty (LWWMap.put "Alice" 150 ts2)

  -- Merge: later timestamp wins
  let merged := LWWMap.merge board1 board2

  (merged.get "Alice") ≡ some 150

test "multiple players, different servers" := do
  let server1 : ReplicaId := 1
  let server2 : ReplicaId := 2

  let ts1 := LamportTs.new 1 server1
  let ts2 := LamportTs.new 1 server2

  -- Server 1 records Alice and Bob
  let board1 := LWWMap.empty
    |> fun s => LWWMap.apply s (LWWMap.put "Alice" 100 ts1)
    |> fun s => LWWMap.apply s (LWWMap.put "Bob" 80 ts1)

  -- Server 2 records Carol and Dave
  let board2 := LWWMap.empty
    |> fun s => LWWMap.apply s (LWWMap.put "Carol" 120 ts2)
    |> fun s => LWWMap.apply s (LWWMap.put "Dave" 90 ts2)

  -- Merge combines all players
  let merged := LWWMap.merge board1 board2

  (merged.get "Alice") ≡ some 100
  (merged.get "Bob") ≡ some 80
  (merged.get "Carol") ≡ some 120
  (merged.get "Dave") ≡ some 90

/-! ## Social Network with TwoPGraph

Friend relationships in a social network.
TwoPGraph allows adding and removing vertices (users) and edges (friendships).
Once removed, items cannot be re-added (two-phase semantics).
-/

testSuite "Social Network (TwoPGraph)"

test "add users and friendships" := do
  -- Add three users: Alice, Bob, Carol
  let graph := TwoPGraph.empty
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "Alice")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "Bob")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "Carol")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge "Alice" "Bob")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge "Bob" "Carol")

  (graph.containsVertex "Alice") ≡ true
  (graph.containsVertex "Bob") ≡ true
  (graph.containsVertex "Carol") ≡ true
  (graph.containsEdge "Alice" "Bob") ≡ true
  (graph.containsEdge "Bob" "Carol") ≡ true
  (graph.containsEdge "Alice" "Carol") ≡ false

test "unfriend removes edge but keeps users" := do
  let graph := TwoPGraph.empty
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "Alice")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "Bob")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge "Alice" "Bob")
    |> fun g => TwoPGraph.apply g (TwoPGraph.removeEdge "Alice" "Bob")

  (graph.containsVertex "Alice") ≡ true
  (graph.containsVertex "Bob") ≡ true
  (graph.containsEdge "Alice" "Bob") ≡ false

test "delete account removes user and their friendships" := do
  let graph := TwoPGraph.empty
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "Alice")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "Bob")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "Carol")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge "Alice" "Bob")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge "Alice" "Carol")
    |> fun g => TwoPGraph.apply g (TwoPGraph.removeVertex "Alice")

  (graph.containsVertex "Alice") ≡ false
  (graph.containsVertex "Bob") ≡ true
  (graph.containsVertex "Carol") ≡ true
  -- Alice's friendships are hidden when she's removed
  (graph.containsEdge "Alice" "Bob") ≡ false
  (graph.containsEdge "Alice" "Carol") ≡ false

test "concurrent friend and unfriend from different servers" := do
  -- Note: TwoPGraph doesn't use replica IDs directly - operations are global
  -- Initial state: Alice and Bob exist with friendship
  let initial := TwoPGraph.empty
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "Alice")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addVertex "Bob")
    |> fun g => TwoPGraph.apply g (TwoPGraph.addEdge "Alice" "Bob")

  -- Server 1: Alice unfriends Bob
  let s1 := TwoPGraph.apply initial (TwoPGraph.removeEdge "Alice" "Bob")

  -- Server 2: (doesn't know about unfriend) - no-op since edge exists
  let s2 := initial

  -- Merge: remove wins (two-phase semantics)
  let merged := TwoPGraph.merge s1 s2

  (merged.containsEdge "Alice" "Bob") ≡ false

/-! ## Inventory System with PNMap

Track inventory quantities across multiple warehouses.
PNMap maps product IDs to PNCounters, allowing increment and decrement.
-/

testSuite "Inventory System (PNMap)"

test "receive stock at different warehouses" := do
  let warehouse1 : ReplicaId := 1
  let warehouse2 : ReplicaId := 2

  -- Warehouse 1 receives 10 units of SKU-001
  let inv1 := PNMap.empty
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse1)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse1)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse1)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse1)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse1)

  -- Warehouse 2 receives 3 units
  let inv2 := PNMap.empty
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse2)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse2)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse2)

  -- Total inventory after sync
  let merged := PNMap.merge inv1 inv2

  (merged.get "SKU-001") ≡ 8

test "ship from warehouse decrements stock" := do
  let warehouse : ReplicaId := 1

  -- Receive 5 units, ship 2
  let inv := PNMap.empty
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse)
    |> fun m => PNMap.apply m (PNMap.decrement "SKU-001" warehouse)
    |> fun m => PNMap.apply m (PNMap.decrement "SKU-001" warehouse)

  (inv.get "SKU-001") ≡ 3

test "concurrent shipments from different warehouses" := do
  let warehouse1 : ReplicaId := 1
  let warehouse2 : ReplicaId := 2

  -- Start with 10 units total (5 each)
  let initial := PNMap.empty
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse1)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse1)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse1)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse1)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse1)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse2)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse2)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse2)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse2)
    |> fun m => PNMap.apply m (PNMap.increment "SKU-001" warehouse2)

  -- Warehouse 1 ships 2 units (concurrent)
  let inv1 := initial
    |> fun m => PNMap.apply m (PNMap.decrement "SKU-001" warehouse1)
    |> fun m => PNMap.apply m (PNMap.decrement "SKU-001" warehouse1)

  -- Warehouse 2 ships 3 units (concurrent)
  let inv2 := initial
    |> fun m => PNMap.apply m (PNMap.decrement "SKU-001" warehouse2)
    |> fun m => PNMap.apply m (PNMap.decrement "SKU-001" warehouse2)
    |> fun m => PNMap.apply m (PNMap.decrement "SKU-001" warehouse2)

  -- Total: 10 - 2 - 3 = 5
  let merged := PNMap.merge inv1 inv2

  (merged.get "SKU-001") ≡ 5

/-! ## Collaborative Text Editor with Fugue

Real-time collaborative editing where multiple users type concurrently.
Fugue ensures that concurrent insertions at the same position don't interleave
character-by-character (maximal non-interleaving property).
-/

testSuite "Collaborative Text Editor (Fugue)"

test "Bob starts typing on line 2 while Alice finishes line 1" := do
  -- Alice is typing "Hello" on line 1
  -- After Alice types "He", Bob receives the document
  -- Bob adds a newline and starts typing "World" on line 2
  -- Alice continues with "llo" concurrently
  -- Merge should cleanly produce "Hello\nWorld"
  let alice : ReplicaId := 1
  let bob : ReplicaId := 2

  -- Alice types "He"
  let (_, doc) := Fugue.insertAt Fugue.empty alice 0 'H'
  let (_, docHe) := Fugue.insertAt doc alice 1 'e'

  -- Bob receives "He", adds newline, starts typing "World" on line 2
  let (_, doc) := Fugue.insertAt docHe bob 2 '\n'
  let (_, doc) := Fugue.insertAt doc bob 3 'W'
  let (_, doc) := Fugue.insertAt doc bob 4 'o'
  let (_, doc) := Fugue.insertAt doc bob 5 'r'
  let (_, doc) := Fugue.insertAt doc bob 6 'l'
  let (_, docBob) := Fugue.insertAt doc bob 7 'd'

  -- Meanwhile, Alice continues typing "llo" (doesn't know about Bob yet)
  let (_, doc) := Fugue.insertAt docHe alice 2 'l'
  let (_, doc) := Fugue.insertAt doc alice 3 'l'
  let (_, docAlice) := Fugue.insertAt doc alice 4 'o'

  -- At this point:
  -- Alice has: "Hello"
  -- Bob has: "He\nWorld"
  -- Alice's "llo" and Bob's "\nWorld" are CONCURRENT (both built on "He")

  (docAlice.toList) ≡ ['H', 'e', 'l', 'l', 'o']
  (docBob.toList) ≡ ['H', 'e', '\n', 'W', 'o', 'r', 'l', 'd']

  -- Merge: Both "llo" and "\nWorld" attach after 'e'
  -- Non-interleaving keeps them grouped
  let merged := Fugue.merge docAlice docBob
  let text := merged.toList

  -- Should have all 11 characters: H e l l o \n W o r l d
  (text.length) ≡ 11

  -- First two chars are "He" (causal - both saw this)
  (text.take 2) ≡ ['H', 'e']

  -- Result is deterministic: "Hello\nWorld"
  -- Alice's "llo" comes first because it's a same-author continuation of 'e'
  -- Bob's "\nWorld" comes after because it's a different author
  let textStr := String.ofList text
  (textStr) ≡ "Hello\nWorld"

test "two users type at start - fully concurrent, blocks stay together" := do
  -- Alice and Bob both start typing at the beginning of an empty document
  let alice : ReplicaId := 1
  let bob : ReplicaId := 2

  -- Alice types "Hello" at position 0
  let (_, doc) := Fugue.insertAt Fugue.empty alice 0 'H'
  let (_, doc) := Fugue.insertAt doc alice 1 'e'
  let (_, doc) := Fugue.insertAt doc alice 2 'l'
  let (_, doc) := Fugue.insertAt doc alice 3 'l'
  let (_, docAlice) := Fugue.insertAt doc alice 4 'o'

  -- Bob types "Hi" at position 0 (concurrent, on empty doc)
  let (_, doc) := Fugue.insertAt Fugue.empty bob 0 'H'
  let (_, docBob) := Fugue.insertAt doc bob 1 'i'

  -- Merge: either "HelloHi" or "HiHello", NOT "HHeillol"
  let merged := Fugue.merge docAlice docBob
  let text := merged.toList

  -- The characters should be grouped, not interleaved
  -- Check that we have all characters
  (text.length) ≡ 7

  -- Either Alice's text comes first or Bob's, but they don't interleave
  let textStr := String.ofList text
  let isAliceFirst := textStr == "HelloHi"
  let isBobFirst := textStr == "HiHello"
  (isAliceFirst || isBobFirst) ≡ true

test "delete character in middle" := do
  let user : ReplicaId := 1

  -- Type "Hello"
  let (_, doc) := Fugue.insertAt Fugue.empty user 0 'H'
  let (_, doc) := Fugue.insertAt doc user 1 'e'
  let (_, doc) := Fugue.insertAt doc user 2 'l'
  let (_, doc) := Fugue.insertAt doc user 3 'l'
  let (_, doc) := Fugue.insertAt doc user 4 'o'

  (doc.toList) ≡ ['H', 'e', 'l', 'l', 'o']

  -- Delete the first 'l' (index 2)
  match Fugue.deleteAt doc 2 with
  | some deleteOp =>
    let doc' := Fugue.apply doc deleteOp
    (doc'.toList) ≡ ['H', 'e', 'l', 'o']
  | none =>
    -- This should not happen, but we need to handle the case
    (false) ≡ true

test "concurrent insert and delete at same position" := do
  let alice : ReplicaId := 1

  -- Start with "ab"
  let (_, doc) := Fugue.insertAt Fugue.empty alice 0 'a'
  let (_, doc) := Fugue.insertAt doc alice 1 'b'

  -- Alice inserts 'X' between 'a' and 'b' (at index 1)
  let (_, docAlice) := Fugue.insertAt doc alice 1 'X'

  -- Concurrent delete of 'b' (at index 1) - simulating another user
  match Fugue.deleteAt doc 1 with
  | some deleteOp =>
    let docBob := Fugue.apply doc deleteOp
    -- Merge: should have 'a', 'X' (Bob's delete removed 'b')
    let merged := Fugue.merge docAlice docBob
    (merged.toList) ≡ ['a', 'X']
  | none =>
    -- This should not happen
    (false) ≡ true

/-! ## Conflict Resolution with MVRegister

When concurrent writes happen, MVRegister preserves ALL values.
The application can then display or resolve the conflict.
MVRegister uses VectorClock to track causality.
-/

testSuite "Conflict Resolution (MVRegister)"

test "concurrent edits preserve both values" := do
  let alice : ReplicaId := 1
  let bob : ReplicaId := 2

  -- Alice and Bob have independent vector clocks (no causal relationship)
  let aliceClock := VectorClock.empty.inc alice
  let bobClock := VectorClock.empty.inc bob

  let initial : MVRegister String := MVRegister.empty

  -- Alice changes title to "Project Alpha"
  let docAlice := MVRegister.apply initial (MVRegister.set "Project Alpha" aliceClock)

  -- Bob changes title to "Alpha Project" (concurrent, independent clock)
  let docBob := MVRegister.apply initial (MVRegister.set "Alpha Project" bobClock)

  -- Merge: both values preserved as concurrent
  let merged := MVRegister.merge docAlice docBob
  let values := merged.get

  (values.length) ≡ 2
  (values.contains "Project Alpha") ≡ true
  (values.contains "Alpha Project") ≡ true

test "later write supersedes earlier on same replica" := do
  let user : ReplicaId := 1

  -- Clock progresses: vc1 -> vc2 (vc2 dominates vc1)
  let vc1 := VectorClock.empty.inc user
  let vc2 := vc1.inc user

  let reg := MVRegister.empty
    |> fun r => MVRegister.apply r (MVRegister.set "Draft" vc1)
    |> fun r => MVRegister.apply r (MVRegister.set "Final" vc2)

  let values := reg.get

  -- Only the latest value remains (vc2 dominates vc1)
  (values.length) ≡ 1
  (values.contains "Final") ≡ true

test "resolve conflict by writing with dominating clock" := do
  let alice : ReplicaId := 1
  let bob : ReplicaId := 2
  let resolver : ReplicaId := 3

  -- Independent clocks = concurrent
  let aliceClock := VectorClock.empty.inc alice
  let bobClock := VectorClock.empty.inc bob

  -- Concurrent edits create conflict
  let docAlice := MVRegister.apply MVRegister.empty (MVRegister.set "A" aliceClock)
  let docBob := MVRegister.apply MVRegister.empty (MVRegister.set "B" bobClock)
  let merged := MVRegister.merge docAlice docBob

  (merged.get.length) ≡ 2

  -- Resolver creates a clock that dominates both by including their history
  let resolverClock := aliceClock.merge bobClock |>.inc resolver

  -- Resolver picks "A" - the new clock dominates both old ones
  let resolved := MVRegister.apply merged (MVRegister.set "A" resolverClock)

  (resolved.get.length) ≡ 1
  (resolved.get) ≡ ["A"]

/-! ## Timestamp-Based Set with LWWElementSet

Per-element timestamps allow last-write-wins semantics for each element.
Useful when elements need individual expiration or update times.
-/

testSuite "Feature Flags (LWWElementSet)"

test "enable feature on one server, disable on another - later wins" := do
  let devServer : ReplicaId := 1
  let prodServer : ReplicaId := 2

  -- Dev enables dark_mode at time 1
  let devTs := LamportTs.new 1 devServer
  let devFlags := LWWElementSet.apply LWWElementSet.empty
    (LWWElementSet.add "dark_mode" devTs)

  -- Prod disables dark_mode at time 2 (later)
  let prodTs := LamportTs.new 2 prodServer
  let prodFlags := LWWElementSet.apply LWWElementSet.empty
    (LWWElementSet.remove "dark_mode" prodTs)

  -- Merge: later timestamp wins
  let merged := LWWElementSet.merge devFlags prodFlags

  (merged.contains "dark_mode") ≡ false

test "multiple features independently managed" := do
  let server1 : ReplicaId := 1
  let server2 : ReplicaId := 2

  let ts1 := LamportTs.new 1 server1
  let ts2 := LamportTs.new 2 server2

  let flags := LWWElementSet.empty
    |> fun s => LWWElementSet.apply s (LWWElementSet.add "feature_a" ts1)
    |> fun s => LWWElementSet.apply s (LWWElementSet.add "feature_b" ts1)
    |> fun s => LWWElementSet.apply s (LWWElementSet.remove "feature_a" ts2)

  (flags.contains "feature_a") ≡ false  -- removed at later time
  (flags.contains "feature_b") ≡ true   -- still enabled

/-! ## Document Viewers with GSet

Track who has viewed a document. GSet is grow-only, perfect for
recording events that can never be "unread" or undone.
-/

testSuite "Document Viewers (GSet)"

test "viewers from different servers are combined" := do
  -- Each server tracks who viewed the document
  let usServer := GSet.empty
    |> fun s => GSet.apply s (GSet.add "alice@example.com")
    |> fun s => GSet.apply s (GSet.add "bob@example.com")

  let euServer := GSet.empty
    |> fun s => GSet.apply s (GSet.add "carol@example.com")
    |> fun s => GSet.apply s (GSet.add "dave@example.com")

  -- Sync: all viewers combined
  let synced := GSet.merge usServer euServer

  (synced.contains "alice@example.com") ≡ true
  (synced.contains "bob@example.com") ≡ true
  (synced.contains "carol@example.com") ≡ true
  (synced.contains "dave@example.com") ≡ true
  (synced.size) ≡ 4

test "duplicate views are idempotent" := do
  -- Alice views the document multiple times from different devices
  let viewers := GSet.empty
    |> fun s => GSet.apply s (GSet.add "alice@example.com")
    |> fun s => GSet.apply s (GSet.add "alice@example.com")  -- duplicate
    |> fun s => GSet.apply s (GSet.add "alice@example.com")  -- duplicate

  (viewers.size) ≡ 1
  (viewers.contains "alice@example.com") ≡ true

test "once viewed, always viewed - cannot be unread" := do
  -- GSet has no remove operation - this is intentional
  -- Once someone views a document, that view is permanent
  let viewers := GSet.empty
    |> fun s => GSet.apply s (GSet.add "alice@example.com")

  -- There's no way to remove Alice from viewers - perfect for audit logs
  (viewers.contains "alice@example.com") ≡ true

/-! ## Redeemable Coupons with TwoPSet

One-time coupon codes that can be redeemed once and never re-added.
TwoPSet's two-phase semantics are perfect for this use case.
-/

testSuite "Redeemable Coupons (TwoPSet)"

test "coupon can be redeemed once" := do
  -- Start with available coupons
  let coupons := TwoPSet.empty
    |> fun s => TwoPSet.apply s (TwoPSet.add "SAVE20")
    |> fun s => TwoPSet.apply s (TwoPSet.add "FREESHIP")

  (coupons.contains "SAVE20") ≡ true
  (coupons.contains "FREESHIP") ≡ true

  -- Customer redeems SAVE20
  let afterRedeem := TwoPSet.apply coupons (TwoPSet.remove "SAVE20")

  (afterRedeem.contains "SAVE20") ≡ false  -- Redeemed!
  (afterRedeem.contains "FREESHIP") ≡ true  -- Still available

test "redeemed coupon cannot be re-added" := do
  -- Add and redeem a coupon
  let coupons := TwoPSet.empty
    |> fun s => TwoPSet.apply s (TwoPSet.add "SAVE20")
    |> fun s => TwoPSet.apply s (TwoPSet.remove "SAVE20")

  (coupons.contains "SAVE20") ≡ false

  -- Try to add it again - fails due to two-phase semantics
  let tryAgain := TwoPSet.apply coupons (TwoPSet.add "SAVE20")

  (tryAgain.contains "SAVE20") ≡ false  -- Still gone!

test "concurrent redemption from different servers" := do
  -- Both servers have the coupon
  let initial := TwoPSet.apply TwoPSet.empty (TwoPSet.add "SAVE20")

  -- Server 1: customer redeems
  let server1 := TwoPSet.apply initial (TwoPSet.remove "SAVE20")

  -- Server 2: doesn't know about redemption yet
  let server2 := initial

  -- Sync: remove wins (two-phase)
  let merged := TwoPSet.merge server1 server2

  (merged.contains "SAVE20") ≡ false

/-! ## User Profile with LWWRegister

User profile fields that can be updated from multiple devices.
LWWRegister uses timestamps to determine which update wins.
-/

testSuite "User Profile (LWWRegister)"

test "latest profile update wins" := do
  let phone : ReplicaId := 1
  let laptop : ReplicaId := 2

  -- User updates name on phone at time 1
  let ts1 := LamportTs.new 1 phone
  let phoneProfile := LWWRegister.apply LWWRegister.empty (LWWRegister.set "Alice" ts1)

  -- User updates name on laptop at time 2 (later)
  let ts2 := LamportTs.new 2 laptop
  let laptopProfile := LWWRegister.apply LWWRegister.empty (LWWRegister.set "Alice Smith" ts2)

  -- Sync: later timestamp wins
  let merged := LWWRegister.merge phoneProfile laptopProfile

  (merged.get) ≡ some "Alice Smith"

test "concurrent updates resolved by timestamp" := do
  let server1 : ReplicaId := 1
  let server2 : ReplicaId := 2

  -- Same logical time but different servers
  let ts1 := LamportTs.new 5 server1
  let ts2 := LamportTs.new 5 server2

  let profile1 := LWWRegister.apply LWWRegister.empty (LWWRegister.set "Draft Bio" ts1)
  let profile2 := LWWRegister.apply LWWRegister.empty (LWWRegister.set "Final Bio" ts2)

  -- Merge is deterministic (tie-breaker uses value comparison)
  let merged := LWWRegister.merge profile1 profile2

  -- One of them wins deterministically
  (merged.get.isSome) ≡ true

test "empty register has no value" := do
  let reg : LWWRegister String := LWWRegister.empty

  (reg.get) ≡ none

/-! ## Per-Channel Message Counts with ORMap

Track message counts per channel using ORMap with nested PNCounters.
ORMap allows adding/removing channels, and nested CRDTs are merged.
-/

testSuite "Per-Channel Message Counts (ORMap)"

test "add channels with initial counters" := do
  let server1 : ReplicaId := 1
  let tag1 := UniqueId.new server1 0
  let tag2 := UniqueId.new server1 1

  -- Create channels with empty counters
  let channels : ORMap String PNCounter PNCounterOp := ORMap.empty
    |> fun m => ORMap.apply m (ORMap.put "general" PNCounter.empty tag1)
    |> fun m => ORMap.apply m (ORMap.put "random" PNCounter.empty tag2)

  (channels.contains "general") ≡ true
  (channels.contains "random") ≡ true
  (channels.size) ≡ 2

test "increment message count in channel" := do
  let server1 : ReplicaId := 1
  let tag1 := UniqueId.new server1 0

  -- Create channel with counter
  let channels : ORMap String PNCounter PNCounterOp := ORMap.empty
    |> fun m => ORMap.apply m (ORMap.put "general" PNCounter.empty tag1)

  -- Increment message count (nested operation)
  let channels' := ORMap.apply channels (ORMap.update "general" tag1 (PNCounter.increment server1))
  let channels'' := ORMap.apply channels' (ORMap.update "general" tag1 (PNCounter.increment server1))

  -- Check the nested counter value
  match (channels''.get "general").head? with
  | some counter => (counter.value) ≡ 2
  | none => (false) ≡ true

test "delete channel removes it" := do
  let server1 : ReplicaId := 1
  let tag1 := UniqueId.new server1 0

  let channels : ORMap String PNCounter PNCounterOp := ORMap.empty
    |> fun m => ORMap.apply m (ORMap.put "general" PNCounter.empty tag1)

  (channels.contains "general") ≡ true

  -- Delete the channel
  let deleteOp := ORMap.delete channels "general"
  let channels' := ORMap.apply channels deleteOp

  (channels'.contains "general") ≡ false

/-! ## Collaborative Task List with RGA

Shared task list where multiple users can add tasks concurrently.
RGA maintains order and handles concurrent insertions.
-/

testSuite "Collaborative Task List (RGA)"

test "add tasks in sequence" := do
  let user : ReplicaId := 1

  -- Add tasks one after another
  let id1 := UniqueId.new user 0
  let id2 := UniqueId.new user 1
  let id3 := UniqueId.new user 2

  let tasks := RGA.empty
    |> fun r => RGA.apply r (RGA.insert none "Buy groceries" id1)
    |> fun r => RGA.apply r (RGA.insert (some id1) "Walk the dog" id2)
    |> fun r => RGA.apply r (RGA.insert (some id2) "Call mom" id3)

  (tasks.toList) ≡ ["Buy groceries", "Walk the dog", "Call mom"]
  (tasks.length) ≡ 3

test "concurrent task additions at same position" := do
  let alice : ReplicaId := 1
  let bob : ReplicaId := 2

  -- Both start with one task
  let id0 := UniqueId.new alice 0
  let initial := RGA.apply RGA.empty (RGA.insert none "Shared task" id0)

  -- Alice adds "Alice's task" after the shared task
  let aliceId := UniqueId.new alice 1
  let aliceList := RGA.apply initial (RGA.insert (some id0) "Alice's task" aliceId)

  -- Bob adds "Bob's task" after the shared task (concurrent)
  let bobId := UniqueId.new bob 1
  let bobList := RGA.apply initial (RGA.insert (some id0) "Bob's task" bobId)

  -- Merge: both tasks appear, deterministically ordered
  let merged := RGA.merge aliceList bobList

  (merged.length) ≡ 3
  (merged.toList.contains "Shared task") ≡ true
  (merged.toList.contains "Alice's task") ≡ true
  (merged.toList.contains "Bob's task") ≡ true

test "complete task (delete)" := do
  let user : ReplicaId := 1

  let id1 := UniqueId.new user 0
  let id2 := UniqueId.new user 1

  let tasks := RGA.empty
    |> fun r => RGA.apply r (RGA.insert none "Buy groceries" id1)
    |> fun r => RGA.apply r (RGA.insert (some id1) "Walk the dog" id2)

  (tasks.toList) ≡ ["Buy groceries", "Walk the dog"]

  -- Complete first task
  let tasks' := RGA.apply tasks (RGA.delete id1)

  (tasks'.toList) ≡ ["Walk the dog"]

/-! ## Priority Queue with LSEQ

Position-based sequence for maintaining ordered items.
LSEQ uses dense position identifiers for efficient concurrent edits.
-/

testSuite "Priority Queue (LSEQ)"

test "insert items in order" := do
  let user : ReplicaId := 1

  -- Insert items at positions 0, 1, 2
  let (_, queue) := LSEQ.insertAt LSEQ.empty user 0 "High priority"
  let (_, queue) := LSEQ.insertAt queue user 1 "Medium priority"
  let (_, queue) := LSEQ.insertAt queue user 2 "Low priority"

  (queue.toList) ≡ ["High priority", "Medium priority", "Low priority"]
  (queue.length) ≡ 3

test "insert at beginning" := do
  let user : ReplicaId := 1

  -- Start with one item
  let (_, queue) := LSEQ.insertAt LSEQ.empty user 0 "First"

  -- Insert at beginning (index 0)
  let (_, queue) := LSEQ.insertAt queue user 0 "Now first"

  (queue.toList) ≡ ["Now first", "First"]

test "delete from middle" := do
  let user : ReplicaId := 1

  let (_, queue) := LSEQ.insertAt LSEQ.empty user 0 "A"
  let (_, queue) := LSEQ.insertAt queue user 1 "B"
  let (_, queue) := LSEQ.insertAt queue user 2 "C"

  (queue.toList) ≡ ["A", "B", "C"]

  -- Delete "B" (index 1)
  match LSEQ.deleteAt queue 1 with
  | some deleteOp =>
    let queue' := LSEQ.apply queue deleteOp
    (queue'.toList) ≡ ["A", "C"]
  | none =>
    (false) ≡ true

/-! ## Emergency Stop with DWFlag

Safety-critical kill switch where concurrent disables win, but a later
explicit enable can resume the system.
-/

testSuite "Emergency Stop (DWFlag)"

test "emergency stop disable wins on concurrent, later enable resumes" := do
  let sensor1 : ReplicaId := 1
  let sensor2 : ReplicaId := 2

  -- System is running (enabled)
  let running := DWFlag.apply DWFlag.empty (DWFlag.enable (LamportTs.new 1 sensor1))

  (running.value) ≡ true

  -- Sensor 2 triggers emergency stop
  let stopped := DWFlag.apply running (DWFlag.disable (LamportTs.new 2 sensor2))

  -- Later disable wins: system stopped
  (stopped.value) ≡ false

  -- Later enable can resume
  let resumed := DWFlag.apply stopped (DWFlag.enable (LamportTs.new 3 sensor1))

  (resumed.value) ≡ true

test "concurrent enable and disable - disable wins" := do
  let node1 : ReplicaId := 1
  let node2 : ReplicaId := 2

  -- Node 1 enables
  let enabled := DWFlag.apply DWFlag.empty (DWFlag.enable (LamportTs.new 1 node1))

  -- Node 2 disables (concurrent)
  let disabled := DWFlag.apply DWFlag.empty (DWFlag.disable (LamportTs.new 1 node2))

  -- Merge: disable wins
  let merged := DWFlag.merge enabled disabled

  (merged.value) ≡ false

test "contrast with EWFlag - different semantics" := do
  let node1 : ReplicaId := 1
  let node2 : ReplicaId := 2

  -- DWFlag: disable-wins (safety-critical, conservative)
  let dwEnabled := DWFlag.apply DWFlag.empty (DWFlag.enable (LamportTs.new 1 node1))
  let dwDisabled := DWFlag.apply DWFlag.empty (DWFlag.disable (LamportTs.new 1 node2))
  let dwMerged := DWFlag.merge dwEnabled dwDisabled

  -- EWFlag: enable-wins (availability-focused)
  let ewEnabled := EWFlag.apply EWFlag.empty (EWFlag.enable (LamportTs.new 1 node1))
  let ewDisabled := EWFlag.apply EWFlag.empty (EWFlag.disable (LamportTs.new 1 node2))
  let ewMerged := EWFlag.merge ewEnabled ewDisabled

  -- Same operations, opposite results!
  (dwMerged.value) ≡ false  -- DWFlag: disable wins
  (ewMerged.value) ≡ true   -- EWFlag: enable wins

end ConvergentTests.ScenarioTests
