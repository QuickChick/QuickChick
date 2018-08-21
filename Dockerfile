FROM ysli/coq:8.8
ENV QC_VERSION 8.8
RUN . ~/.profile \
 && opam repo add coq-released https://coq.inria.fr/opam/released \
 && git clone --depth 1 -b $QC_VERSION https://github.com/QuickChick/QuickChick \
 && opam pin add QuickChick
