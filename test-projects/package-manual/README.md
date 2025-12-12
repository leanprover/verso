# Demonstration Package Documentation

## What is This?

This is a demonstration of documentation for a Lean package, built in
Verso's manual genre.

To build it, run:

```
$ lake exe packagedocs --output _out/examples/packagedocs
```

## Building Your Own

To base your own book on it, copy the contents of this directory and
add the following files:

`lakefile.toml`:

```
name = "myprojectname"
defaultTargets = ["docs"]

[[require]]
name = "verso"
git = "https://github.com/leanprover/verso"
rev = "nightly-testing"

[[lean_lib]]
name = "PackageManual"

[[lean_exe]]
name = "docs"
root = "PackageManualMain"
```

`lean-toolchain`: use the same as [Verso's](../../lean-toolchain).

In a sibling directory, copy the contents of
[`../documented-package/`](../documented-package/). Make sure that it
depends on the same version of `subverso` as the documentation, but
the toolchains don't need to match.

You can then build your documentation with:

```
$ lake exe docs --output _out/html --depth 2
```
