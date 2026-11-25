# Writing modeled Go

Choose a small operation whose inputs and outputs express a property you want to prove. Let ordinary Go gather input, perform I/O, and display results. Put the decision in a function that takes values and returns unnamed results. A record can carry the next state and observations together, and multiple results become Lean products.

## Keep the model at a value boundary

The bowling API returns a game and an acceptance flag. Its modeled value method returns a `rollResult` record, and the public wrapper unpacks it. The compiler copies source bytes into a `lean.ByteArray` at its public entry point, then works with that value inside the modeled call graph. [Bowling](../examples/proven/bowling/README.md) and [compiler](../examples/proven/stack_machine_compiler/README.md)

Use concrete receivers, explicit immutable local initializers, keyed record literals, `if`, and early returns. Read-only pointer receivers are supported; updates through pointers remain outside the subset. Return a new value when a field changes. A translated method takes its receiver first in Lean, so `game.roll(pins)` becomes an application of `«Game$roll»` to `game` and `pins`. See [runtime boundary types](runtime-boundary-types.md) for nil failure and multiple results.

## Move traversal state into a record

The grid game replays moves with a named step that receives a direction and the current replay state. The state carries the position and wrapping mode. It returns the next position with the same mode:

```go
return lean.FoldList(moves, replayState{Position: Start(), Wrap: wrap}, replayMove).Position
```

Use `FoldN` to visit a known number of indices, `FoldList` to visit list items, and the `Until` variants to stop early. Put extra inputs in the state record. For arrays and byte arrays, iterate over `Size()` and use `Get(index)`. A named step is part of the modeled call graph and must satisfy the same subset rules. [Grid game walkthrough](../examples/proven/grid_game/README.md)

## Give recursive records a decreasing measure

The compiler represents child expressions with direct `lean.Box[expression]` fields. Use `lean.NewBox(value)` for a child and an empty box for absence. Check `IsSome()` before recursively processing `Get()`. The compiler marks its directly recursive passes with `//golean:termination:by sizeOf expr`. Lean checks that the measure decreases at each recursive call and exposes an unfolding equation ending in `.eq_def`. [Compiler walkthrough](../examples/proven/stack_machine_compiler/README.md)

See [Supported Go](supported-go.md) for representations and restrictions.
