FROM coqorg/coq:dev
COPY --chown=coq . QuickChick
ENV OPAMYES true
RUN opam update && opam pin add QuickChick
