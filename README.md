coq-ext-lib
===========
[![CircleCI](https://circleci.com/gh/coq-community/coq-ext-lib.svg?style=svg)](https://circleci.com/gh/coq-ext-lib/coq-ext-lib)
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Gitter][gitter-shield]][gitter-link]

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[gitter-shield]: https://img.shields.io/badge/chat-on%20gitter-%23c1272d.svg
[gitter-link]: https://gitter.im/coq-community/Lobby


A collection of theories and plugins that may be useful in other Coq developments.


## Meta

- Author(s):
  - Gregory Malecha (initial)
- Coq-community maintainer(s):
  - Gregory Malecha ([**@gmalecha**](https://github.com/gmalecha))
  - Yishuai Li ([**@liyishuai**](https://github.com/liyishuai))
- License: [The FreeBSD Copyright](LICENSE)
- Compatible Coq versions: Coq 8.8 or later
- Additional Coq dependencies: none

## Building and installation instructions

The easiest way to install the latest released version of coq-ext-lib
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-ext-lib
```

To instead build and install manually, do:

``` shell
git clone https://github.com/coq-community/coq-ext-lib
cd coq-ext-lib
make theories  # or make -j <number-of-cores-on-your-machine> theories
make install
```

After installation, the included modules are available under
the `ExtLib` namespace.

## Documentation
- [Development version](https://coq-community.github.io/coq-ext-lib/master/toc.html)

Ideas
-----
- Embrace new features, e.g. universe polymorphism, primitive projections, etc.
- Use modules for controlling namespaces.
- Use first-class abstractions where appropriate, e.g. type classes, canonical structures, etc.
  - The library is mostly built around type clases
- Notations should be hidden by modules that are explicitly opened.
  - This avoids clashes between precedence.
  - TB: Actually, this does not completely avoid clashes, if we have to open two modules at the same time (for instance, I often need to open Equality, to get dependent destruction, which conflicts with the rest of my development)
  - TB: I like the idea of having to prefix operations by the name of the module (e.g., DList.fold, DList.map, DList.T), and yet to benefit from the support of notations, without opening this module. I implement that by having a module DList that contains the operations, inside the file DList. The notations live in the file DList, and I do Require Import DList everywhere...
- Avoid the use of the 'core' hint database.
- Avoid the use of dependent functions, e.g. dependendent decidable equality,
  in favor of their boolen counter-parts. Use type-classes to expose the proofs.
-

File Structure
--------------
* theories/
  - Base directory to the provided theories

