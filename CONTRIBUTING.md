# Contribution Guide

## Development

### Build Commands

Use the toplevel `make` to build the whole project:
```
make
```
Makefile will try to find out the number of your CPU cores and parallel as much as
possible.

Once `make` finishes, you can run the binary:
```
dune exec mctt examples/nary.mctt # or your own example
```
or more directly
```
_build/default/driver/mctt.exe examples/nary.mctt # or your own example
```

If you want to profile Coq proofs, you can used
```
make clean
make pretty-timed
```
Note that you need to remove files from a previous build
to check time consumptions of all proofs.

To build Coq proof only, you can go into and only build the `theories` directory:
```
cd theories
make
```

Once you have the executable, you can test the executable with
the examples in `examples` directory using
```
make test
```

### Other Development Commands

One can build coqdoc using
```
make coqdoc
```
on the project root directory.

To build a dependency graph SVG, you can run
```
make depgraphdoc
```
on the project root directory.

In `theories` directory, you can update `_CoqProject` file using
```
make update_CoqProject
```
This will add all `*.v` files in `theories` directory to `_CoqProject`
in the alphabetic order.

The Makefile in `theories` directory also provides two helpful actions
for Menhir parser manangement: `check_parserMessages` and `update_parserMessages`.
- `make check_parserMessages` checks whether parser error messages in 
  `theories/Frontend/parserMessages.messages` contains the complete set of
  error messages for all error cases
- `make update_parserMessages` adds placeholders for missing error cases,
  so that one can complete error messages for those caess.

## Branches

The Github repo includes the following special branches:

1. `main`: the main branch that is used to generate this homepage and Coqdoc;
1. `ext/*`: branches in this pattern are variations of `main` that
   implements various extensions. They are often used to implement
   extensions that require non-trivial workload and are aimed to be
   merged to `main` eventually;
1. `icfp25`: the branch containing artifact for the ICFP'25 publication[^1];
1. `gh-pages`: the branch to host the homepage.

When you want to add a feature that would take more than a month, then
please add an `ext/<feature name>` branch by yourself or request one.

[^1]: Junyoung Jang, Antoine Gaulin, Jason Z.S. Hu, and Brigitte Pientka. 2025. McTT: A Verified Kernel for a Proof Assistant. _Proc. ACM Program. Lang._, ICFP (2025), https://doi.org/10.1145/3747511

## Continuous Integration (CI)

We use GitHub Actions as our CI service, based on our custom docker
image built from `.github/Dockerfile`.

To update the docker image, you need to follow the next steps:

1. Update `.github/Dockerfile`
2. Run https://github.com/Beluga-lang/McTT/actions/workflows/docker.yaml action by clicking "Run workflow" button

Once the workflow succeeds, any future CI will use the new image.
