FROM ysli/coq:dev
ENV QC_VERSION dev
RUN . ~/.profile \
 && opam repo add coq-released https://coq.inria.fr/opam/released \
 && opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev \
 && git clone --depth 1 -b $QC_VERSION https://github.com/QuickChick/QuickChick \
 && opam pin add QuickChick
