FROM coqorg/coq:8.12-ocaml-4.09-flambda
COPY --chown=coq . QuickChick
ENV OPAMYES true
RUN opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev \
 && opam update \
 && opam pin add coq-quickchick QuickChick
