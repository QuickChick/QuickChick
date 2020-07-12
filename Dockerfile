FROM coqorg/coq:dev-ocaml-4.09-flambda
COPY --chown=coq . QuickChick
ENV OPAMYES true
RUN opam update && opam pin add coq-quickchick QuickChick
