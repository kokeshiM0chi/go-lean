# CLI and directive reference

Run from the Go module root. In a checkout of go-lean, replace `go tool go-lean` with `go run ./cmd/go-lean`.

| Command | Result |
| --- | --- |
| `go tool go-lean setup` | Initialize the Lean workspace, preserving existing configuration. |
| `go tool go-lean doctor` | Check workspace and toolchain prerequisites. |
| `go tool go-lean transpile ./pkg` | Generate the selected package's Lean files and modeled dependencies. |
| `go tool go-lean transpile ./...` | Generate across the module and reconcile managed artifacts. |
| `go tool go-lean verify ./pkg` | Generate and check the selected package. |
| `go tool go-lean verify` | Generate and check the workspace. |

Package selectors include `.`, `./pkg`, `./pkg/...`, and `./...`. See [Writing and checking proofs](verification.md) for Lake configuration and troubleshooting.

## Go directives

Use the exact `//golean:` prefix in Go doc comments.

| Directive | Purpose |
| --- | --- |
| `//golean:export` | Select an operation for modeling and allow concrete calls from another modeled Go package. |
| `//golean:verify name : proposition` | Declare a package-unique law. On a function or method, select that operation for modeling. |
| `//golean:verify+ continuation` | Continue a law on consecutive lines. |
| `//golean:verify:import Lean.Module` | Import one Lean module from a package doc comment. |
| `//golean:assume name : proposition` | Declare a law about a scalar dependency function or interface method. Use its unqualified Go name in the law. |
| `//golean:assume+ continuation` | Continue a dependency law on consecutive lines. |
| `//golean:abstract alias.Function` | Replace a function or interface method call from a verified root with a contract parameter. Accepts `Function`, `alias.Function`, `Interface.Method`, or `alias.Interface.Method`. |
| `//golean:termination:by measure` | Supply a Lean `Nat` measure over a directly recursive function's entry parameters. |

## Lean files

| File | Contents |
| --- | --- |
| `<stem>.lean` | Generated model and `Laws` propositions. |
| `<stem>_proofs.lean` | Handwritten proofs, initially scaffolded by generation. |
| `<stem>_verify.lean` | Generated theorem checks and `Checked` exports. |
