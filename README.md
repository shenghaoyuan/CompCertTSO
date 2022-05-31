# CompCertTSO
A Fork from the original [CompCertTSO](https://www.cl.cam.ac.uk/~pes20/CompCertTSO/doc/)

# Dependencies
I only test it on Ubuntu.20, macos may need an older gcc version, see the [discussion](https://discuss.ocaml.org/t/fail-to-compiling-ocaml-base-compiler-3-12-0-on-macos/9933)
- gcc (Ubuntu 9.4.0-1ubuntu1~20.04.1) 9.4.0
- ocaml 3.12.0
- coq 8.3pl5
- ott 0.21.2

# Install

```shell
$ opam switch create compcert-tso ocaml-base-compiler.3.12.0
$ eval $(opam env)
$ opam install Coq=8.3
$ opam install ott=0.21.2
# assumption the current folder is `/home/shyuan/GitHub/`
$ git clone https://github.com/shenghaoyuan/CompCertTSO.git
$ cd CompCertTSO
$ ./configure x86-linux
$ make depend
$ make all
```

Following the original [readme](README), we could test CompCertTSO~~~

# What I do
_All that what I do is make CompCertTSO executable on my Ubuntu_

- Replace [/common/Pointers.v#37.L](/common/Pointers.v#37.L): `Module Ptr.` -> `Module MPtr.`
  - _because I only could install coq8.3pl5 instead of 8.3pl2, the former doesn't allow that a module has the same name as constructor_
- Replace [cil.tar.gz/cil/ocamlutil/perfcount.c.in](cil.tar.gz): #39L removing `static` and #43L removing `inline`
  - _otherwise it returns an error: undefined reference to inline functions_
- Complement three lost sed scripts: see [sed*](clightTSO/clight_src/)
  - _provided by Peter Sewell_
