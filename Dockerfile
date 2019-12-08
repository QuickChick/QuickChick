FROM coqorg/coq:8.10
COPY --chown=coq . QuickChick
ENV OPAMYES true
RUN opam update && opam pin add coq-quickchick QuickChick
