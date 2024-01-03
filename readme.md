# Build Instructions

GHC 8.10.7, cabal 3.4.1.0

```sh
cabal install --lib regex-compat old-time
cabal install happy
make fixcalc
```

Other dependencies:

```console
$ ls
fixcalc
omega_stub
hipsleek

$ (cd hipsleek/omega_modified; make oc) # see hipsleek readme

$ (cd omega_stub; make)

$ cd fixcalc; make fixcalc
```
