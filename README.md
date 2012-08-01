coq-ext-lib
===========

A collection of theories and plugins that may be useful in other Coq developments.

Ideas
-----
- Use modules for controlling namespaces.
- Avoid functors in favor of type classes since type classes are more flexible
  b/c they are first-class.
- Notations should be hidden by modules that are explicitly opened.
  - This avoids clashes between precedence.
- Avoid the use of the 'core' hint database.
- Avoid the use of dependent functions, e.g. dependendent decidable equality,
  in favor of their boolen counter-parts. Use type-classes to expose the proofs.
- 

File Structure
--------------
* plugins/
  - Base directory to the provided plugins
* theories/
  - Base directory to the provided theories

