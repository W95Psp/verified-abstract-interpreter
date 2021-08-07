# Verified Functional Programming of an Abstract Interpreter

This git repository contains the source of the abstract interpreter
presented in our paper *Verified Functional Programming of an Abstract
Interpreter*.

Thanks to [nix](https://nixos.org/), our work is entierly
reproducible, in a few lines of bash:
```bash
sh <(curl -L https://nixos.org/nix/install) --daemon # Install the Nix package manager
git clone https://github.com/W95Psp/verified-abstract-interpreter # Clone this repo
cd verified-abstract-interpreter
nix-build --attr all # Build
```

[PDF of the paper](dist/paper.pdf)

> **Paper abstract.** Abstract interpreters are complex pieces of software: even if the
> abstract interpretation theory and companion algorithms are well
> understood, their implementations are subject to bugs, that might
> question the soundness of their computations.
> 
> While some formally verified abstract interpreters have been written
> in the past, writing and understanding them requires expertise in the
> use of proof assistants, and requires a non-trivial amount of
> interactive proofs.
> 
> This paper presents a formally verified abstract interpreter fully
> programmed and proved correct in the F* verified programming
> environment. Thanks to F* refinement types and SMT prover capabilities
> we demonstrate a substantial saving in proof effort compared to
> previous works based on interactive proof assistants.
> 
> Almost all the code of our implementation, proofs included, written in
> a functional style, are presented directly in the paper.

## Folder structure 📂

This repository is organized as following.
 - `src` contains all the F* source code:
   + `src/core` contains the abstract interpreter itself, every
      definition presented in the paper lives in this directory;
   + `src/app` contains the command line frontend to the abstract
	  interpreter;
   + `src/js` contains the sources of the web wrapper.
 - `latex` contains LaTeX supplementary files, but the paper is
   written as F* comments directly in the modules available under
   `src/code`.
 - `tests` contains a set of unit tests for the abstract interpreter.

**Note:** building the abstract interpreter triggers a build of F* and
Z3 from scratch, which requires about 30 minutes on my machine.

## How to build the abstract interpreter ⚙
### 1. Installing the Nix package manager

> Install Nix on any Linux distribution, MacOS and Windows (via WSL)
> via the recommended multi-user installation:
>
> `sh <(curl -L https://nixos.org/nix/install) --daemon` – [Nix website](https://nixos.org/guides/install-nix.html)

### 2. Build everything
The command `nix-build --attr all` creates the directory `result` with:
 - `bin/analyser`: the binary for the abstract interpretor (`./analyser --help` explain its usage);
 - `examples`: the example programs, `make` to run every test;
 - `paper.pdf`, `paper.tex`: the paper;
 - `test-report.log`: the log report for tests;
 - `typechecking.log`: the output of F* typechecking the abstract interpreter.
  
## Get a developpement environment 🧰
All the steps below require `nix` to be installed (`sh <(curl -L https://nixos.org/nix/install) --daemon`).
 
#### Ready-to-use, preconfigured Emacs
A single line of bash:
```nix-shell --attr shellNix --run preconfigured-emacs```

will open Emacs configured with the correct Z3 and F* binaries in
PATH, with [`fstar-mode`](https://github.com/FStarLang/fstar-mode.el)
configured, and the important modules opened.

#### Pull the F* version we use
`nix-shell --attr shellNix` will drop you in a shell with the correct
`fstar.exe` in PATH.

#### Recompile the analyser
Just run again `nix-build --attr analyser`.

## Try the analyser in your web browser 🌐
### Hosted version
Just go to https://w95psp.github.io/verified-abstract-interpreter

### Locally
Compile the analyser to JavaScript and run a server locally:

`nix-shell --attr webapp-nix-shell --run httpserver`

Then open `http://localhost:8251/` in a web browser.


## Other build recipies availables 💉
 - `nix-build --attr analyser`: builds the binary in `./result/analyser`;
 - `nix-build --attr js-analyser`: builds the web application version of the analyser in `./result/analyser`;
 - `nix-build --attr fstar`: builds the version we use of F* in `./result/bin/fstar.exe`;
 - `nix-build --attr latex -o paper.tex`: builds the latex of the paper as `./paper.tex`;
 - `nix-build --attr ocaml`: extract the abstract interpreter as OCaml code in `./result/`;
 - `nix-build --attr pdf -o paper.pdf`: builds the PDF for the paper as `paper.pdf`;
 - `nix-build --attr tests -o tests.log`: run the tests;
 - `nix-build --attr typecheck -o typecheck.log`: typecheck all the modules with F*.

## Note on reproducability and on Nix ✨
> Nix builds packages in isolation from each other. This ensures that
> they are reproducible and don't have undeclared dependencies, so if
> a package works on one machine, it will also work on another. – https://nixos.org/
### Pointers on Nix
 - https://nixos.org/
 - https://www.tweag.io/blog/2020-06-18-software-heritage/
 - https://serokell.io/blog/what-is-nix

### Flakes
The abstract interpreter actually uses the recent [Nix Flakes](https://nixos.wiki/wiki/Flakes).
If you happen to have flakes enabled on your machine, you can:
 - `nix build .#any-of-the-targets-above`;
 - `nix run .#emacs`;
 - `nix run .#webapp`.


