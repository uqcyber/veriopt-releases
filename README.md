# Veriopt

[![Build](https://github.com/uqcyber/veriopt-releases/actions/workflows/build.yml/badge.svg)](https://github.com/uqcyber/veriopt-releases/actions/workflows/build.yml)

Veriopt is a formal verification effort undertaken by researchers at the University of Queensland. The project aims to formally verify the optimization phases within the [GraalVM](http://graalvm.org/) compiler.

The intermediate representation of the compiler is formalized within the [Isabelle/HOL](https://isabelle.in.tum.de/) interactive theorem prover. Optimizations are then proven to be semantic preserving transformations of the intermediate representation.

This artifact focuses primarily on validating the Isabelle IR graph semantics using unit tests translated from the GraalVM unit tests (Section III of the paper).  However, the Isabelle/HOL theories used to validate binary arithmetic operators (Section II of the paper) and some examples of validating conditional elimination optimizations (Section IV of the paper) are also included and can be viewed using the Isabelle/HOL prover.

## Overview of Repository Contents

This repository contains:

* 'unittest_translations' folder: the GraalVM unit tests translated from Java into Isabelle syntax (*.test files).
  NOTE: The translation code itself is not included in this artifact, but can be viewed in our branch of the [GraalVM repository](https://github.com/uqcyber/graal/tree/veriopt/isabelle-unittests) - the main translation class is [VeriOptGraphTranslator.java](https://github.com/uqcyber/graal/blob/veriopt/isabelle-unittests/compiler/src/org.graalvm.compiler.core/src/org/graalvm/compiler/core/veriopt/VeriOptGraphTranslator.java).
 
* 'unittest_theories_backup' folder: a backup copy of the unit tests packaged up into Isabelle theories of around 1000 lines each, plus the output files from running those tests through the Isabelle prover.

* 'bin' folder: several Bash shell scripts for automating various stages of the testing process.

* 'unittest_run_output.log' file: example Isabelle output when proving ALL unit test theories.

* 'Tests' folder: the working directory where Isabelle unit testing files are generated and run.

* Other folders starting with a capital letter: the supporting Isabelle theories for IR graphs etc.


## Validating Arithmetic Operator Semantics (Section II of paper)

Change into the 'veriopt-releases' directory, view the Isabelle/HOL theory file Tests/ArithmeticTesting.thy.  

You can view this theory using any text editor, but to fully check its contents you will need to view it using the Isabelle/HOL prover version 2022.  That is, run the command:

* isabelle jedit -d . Tests/ArithmeticTesting.thy

If you do not have Isabelle installed on your computer, it is included in the VirtualBox image, as described in the following section.


## Validating GraalVM IR Graph Semantics (Section III of paper)

Note: step 2 below requires the Isabelle 2022 theorem prover, so if you do not have that already 
installed on your computer, we recommend that you perform all these steps inside the following
VirtualBox image which has Ubuntu 2022.10 with Isabelle installed plus a copy of this repository.

* [VirtualBox Image](https://figshare.com/ndownloader/files/39023720)

* The username/password for this VirtualBox image is: vboxuser / veriopt2023

* Note that this VirtualBox image was built using VirtualBox 7.0.6 on Windows.  The image uses Ubuntu 20.10 and defaults to 4 cores and 16Gb RAM.  This is really the minimum requirements for Isabelle, but it should be possible to run most of the generated UnitTestsNN.thy files through Isabelle with only 12Gb of RAM, and perhaps some with 8Gb.

Step 0: change into the 'veriopt-releases' directory.


Step 1: package up the translated tests into Isabelle theories.

* run the command: ./bin/unittest_create.sh

This will create 43 output theories in Tests/UnitTests*.thy


Step 2: run Isabelle on one (or more) of the generated theory files.  For example, UnitTests18.thy:

* run the command: ./bin/unittest_run.sh Tests/UnitTests18.thy

Note that each theory file contains many tests so will take 1-3 minutes to run.
You can run multiple files using wildcards if you wish.
For example, to run ALL tests through Isabelle: 
    ./bin/unittest_run.sh Tests/UnitTests*.thy


Step 3: inspect the summary log for the number of passing and failing tests

* run the command: cat Tests/UnitTests18.log
  Or to see a summary of all results, run: ./bin/unittest_summary.sh

Note that generated theories 14 and 18 should each contain two failing tests, theories 19 and 20 should each contain one failing test, and the remaining *.thy files should have zero test failures.  This is a total of 6 failing tests out of 2642 translated unit tests.  A full set of the expected output *.log files can be seen in the 'unittest_theories_backup' folder.

## Validating Optimization Transformations (Section IV of paper)

Change into the 'veriopt-releases' directory, then view the Isabelle/HOL theory file Tests/MostConditionalEliminationTests.thy.  That is, run the command:

* isabelle jedit -d . Tests/MostConditionalEliminationTests.thy


You can view this theory using any text editor, but to fully check its contents you will need to view it using the Isabelle/HOL prover version 2022.  If you do not have that tool installed on your computer, it is included in the VirtualBox image, as described in the above section.


## Viewing Other Supporting Theories

The theories developed as part of this project are automatically built as HTML and deployed for viewing at the below URL:

https://uqcyber.github.io/veriopt-releases

This page provides an overview for each of the Isabelle sessions. You can navigate the theories through the links on the index page. Documentation in the form of PDFs for all relevant theories can also be found at the following locations:

Full document: https://uqcyber.github.io/veriopt-releases/Document/document.pdf

Outline, ignoring proof details: https://uqcyber.github.io/veriopt-releases/Document/outline.pdf

