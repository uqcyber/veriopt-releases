# Veriopt

[![Build](https://github.com/uqcyber/veriopt-releases/actions/workflows/build.yml/badge.svg)](https://github.com/uqcyber/veriopt-releases/actions/workflows/build.yml)

Veriopt is a formal verification effort undertaken by researchers at the University of Queensland. The project aims to formally verify the optimization phases within the [GraalVM](http://graalvm.org/) compiler.

The intermediate representation of the compiler is formalized within the [Isabelle/HOL](https://isabelle.in.tum.de/) interactive theorem prover. Optimizations are then proven to be semantic preserving transformations of the intermediate representation.

This repository hosts the [Isabelle/HOL](https://isabelle.in.tum.de/) theories which define a formal semantics of the intermediate representation and prove the correctness of optimization phases. The repository is in a pre-release state as we develop the theory, the theories including the formal semantics may change frequently.

## Viewing Theories
The theories developed as part of this project are automatically built as HTML and deployed for viewing at the below URL:

https://uqcyber.github.io/veriopt-releases

This page provides an overview for each of the Isabelle sessions. You can navigate the theories through the links on the index page. Documentation in the form of PDFs for all relevant theories can also be found at the following locations:

Full document: https://uqcyber.github.io/veriopt-releases/Document/document.pdf

Outline, ignoring proof details: https://uqcyber.github.io/veriopt-releases/Document/outline.pdf

The theories can also be viewed interactively within the Isabelle/HOL IDE. Instructions on how to do so 
are provided below.

## Setup

### Repository setup
All of the Isabelle theories for this project are contained within this repository. First we will clone
a local copy to access the theories.

```bash
git clone https://github.com/uqcyber/veriopt-releases
```

### Isabelle setup

In order to build, edit and interactively view the theories, you will need access to the `isabelle`
command which is bundled with the Isabelle2025 installation. On the 
[Isabelle2025 installation website](https://isabelle.in.tum.de/website-Isabelle2025/installation.html), 
find your operating system and follow the installation and setup instructions. Once complete, you should
have an unpacked `Isabelle2025` directory on your system. Follow the additional instructions for your 
operating system below to access the `isabelle` command.

#### Linux

The `isabelle` tool is located inside the `Isabelle2025/bin` directory. It is recommended that you add
this directory to your PATH to access the `isabelle` command from anywhere on your system. 

#### macOS

Move the Isabelle2025 `.app` into the `/Applications` folder.

The `isabelle` tool is located inside the `Isabelle2025.app/bin` directory. It is recommended
that you add this directory to your PATH to access the `isabelle` command from anywhere on your system.

#### Windows

Open command prompt and navigate to the `Isabelle2025` directory

```bash
cd Isabelle2025
```

Run the `Cygwin-Terminal` batch file

```bash
Cygwin-Terminal.bat
```

From this terminal, the `isabelle` command can be accessed from anywhere on your system.

## Editing Theories
Theories can be modified within the Isabelle/HOL IDE using the following commands.

```bash
cd veriopt-releases
isabelle jedit -d . ROOT
```

### Pre-compiling theories

These theories are fairly large and require 32GB of RAM to load interactively. 
If you do not have that luxury, you can pre-compile the most memory-intensive theories
(e.g. IRStepThms.thy).
These are included in the Semantics session so we will compile that.

```bash
cd veriopt-releases  # or veriopt-dev/isabelle
isabelle build -d . -v Semantics
isabelle jedit -d . -l Semantics ROOT
```
In the Theories sidebar, you'll see Semantics instead of HOL, meaning we
are using the veriopt/Semantics session.
As a side-effect of this precompilation, you'll be prevented from editing
theories within Semantics ("Cannot update finished theory").

## Building Theories
Building the theories will check all the theories in the repository are correct and generate HTML and PDF outputs. You can build the theories with the following commands.

```bash
cd veriopt-releases
isabelle build -P. -D . -v
```

Generated HTML and PDF artifacts will be available in the `veriopt` directory within the repository.
