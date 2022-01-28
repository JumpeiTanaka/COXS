# COXS

## Installation

* To build the `coxs` command line tool, the following softwares must be installed:
  * GNU Make >= 4.1
  * ocaml >= 4.07.0: see OCaml's [installation guidance](https://ocaml.org/docs/install.html)
  * Ocaml packages:
    * num (>= 1.0): `opam install num`
    * postgresql-ocaml (>=4.0.1): `opam install postgresql`

* Compiling:
  * Clean:
    ```bash
    make clean
    ```
  * Build:
    ```bash
    make all
    ```
  * Release:
    ```bash
    make release
    ```
* Installing:
  ```bash
  make install
  ```

See the usage of the `coxs` command by typing:
  ```bash
  coxs -help
  ```

## Integrated systems

COXS is integrated with BIRDS and its integrated other systems.
Please follow installation guide of BIRDS at [https://github.com/dangtv/BIRDS](https://github.com/dangtv/BIRDS).
