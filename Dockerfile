FROM coqorg/coq:8.8-ocaml-4.09.0-flambda
COPY --chown=coq . QuickChick
ENV OPAMYES true
RUN opam update && opam pin add QuickChick
