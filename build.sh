#!/bin/sh

# Script adapted from https://github.com/wkolowski/Typonomikon

coq_makefile -R "." SeminarInduction -arg "-async-proofs-cache force" -o makefile $(find . -name "*v")
make -j `nproc`
rm makefile makefile.conf .makefile.d

coqdoc src/*v                                             \
       -d docs                                            \
       --html                                             \
       --with-header assets/header.html                   \
       --with-footer assets/footer.html                   \
       --no-lib-name                                      \
       --lib-subtitles                                    \
       --parse-comments                                   \
       --no-index

cp assets/* docs/
mv docs/Seminar.html docs/index.html
