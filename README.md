<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# EdwardsEllipticCurve

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/thery/EdwardsEllipticCurve/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/thery/EdwardsEllipticCurve/actions/workflows/docker-action.yml





Following The Group Law for Edwards Curves Thomas C. Hales

## Meta

- Author(s):
  - Laurent Théry
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.19 or later
- Additional dependencies:
  - [MathComp ssreflect 2.2 or later](https://math-comp.github.io)
- Coq namespace: `edwards`
- Related publication(s): none

## Building and installation instructions

To build and install manually, do:

``` shell
git clone https://github.com/thery/EdwardsEllipticCurve.git
cd EdwardsEllipticCurve
make   # or make -j <number-of-cores-on-your-machine> 
make install
```



