FROM coqorg/coq:8.7
COPY --chown=coq . QuickChick
ENV OPAMYES true
RUN opam pin add QuickChick
