FROM ysli/coq
RUN . ~/.profile \
 && opam repo add coq-released https://coq.inria.fr/opam/released \
 && opam install coq-mathcomp-ssreflect \
 && git clone -b trunk https://github.com/QuickChick/QuickChick.git \
 && make -C QuickChick -j install
