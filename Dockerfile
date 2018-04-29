FROM ysli/coq:8.7
RUN . ~/.profile \
 && opam repo add coq-released https://coq.inria.fr/opam/released \
 && opam install coq-quickchick
