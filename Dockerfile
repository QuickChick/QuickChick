FROM ysli/coq
RUN . ~/.profile \
 && opam repo add coq-released https://coq.inria.fr/opam/released \
 && opam install coq-mathcomp-ssreflect coq-ext-lib \
 && git clone https://github.com/QuickChick/QuickChick.git \
 && make -C QuickChick -j install
