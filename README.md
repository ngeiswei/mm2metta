# mm2metta

Python script to convert [Metamath](https://us.metamath.org/) file to
[MeTTa](https://metta-lang.dev/).  It is derived from
[mmverify.py](https://github.com/david-a-wheeler/mmverify.py), a
Metamath verifier written in Python, originally by Raph Levien.

## Prerequisite

In order to properly work, the proofs have to be fully unpacked.  To do
that you may use the [metamath tool](https://us.metamath.org/#downloads)
as follows

```bash
./metamath "read 'METAMATH_SRC'" "save proof * / normal" "write source 'METAMATH_DST'" "exit"
```

where `METAMATH_SRC` and `METAMATH_DST` are the source and destination
metamath files of interest.  `METAMATH_SRC` can be the same as
`METAMATH_DST`.

## Usage

```
./mm2metta.py METAMATH_SRC > METTA_DST
```

where `METAMATH_SRC` is a MetaMath source file and `METTA_DST` is the
target file where to write the conversion.  By default the arguments
of the inference rules are in reversed order, because it can make
proof search faster.  To switch off the reversing, go to mm2metta.py
and look for the `reverse_argument_order` attribute of `ToMeTTa`.
Likewise, by default variables are not prefixed by a dollar sign, in
order to change that look for the `dollar_variable` attribute of
`ToMeTTa`.

## Lisence

This software is free-libre / open source software (FLOSS) released
under the MIT license.
