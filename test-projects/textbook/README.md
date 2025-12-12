This is a demonstration of a textbook built in Verso's manual genre.

To build it, run:

```
$ lake exe demotextbook --output _out/examples/demotextbook --depth 2
```

To base your own book on it, copy the contents of this directory and
add the following files:

`lakefile.toml`:

```
name = "myprojectname"
defaultTargets = ["textbook"]

[[require]]
name = "verso"
git = "https://github.com/leanprover/verso"
rev = "main"

[[lean_lib]]
name = "DemoTextbook"

[[lean_exe]]
name = "textbook"
root = "DemoTextbookMain"
```

`lean-toolchain`:

```
leanprover/lean4:v4.19.0-rc2
```

You can then build your book with:

```
$ lake exe textbook --output _out/html --depth 2
```
