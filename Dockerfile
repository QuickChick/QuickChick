FROM coqorg/coq:8.8.2
COPY --chown=coq . QuickChick
ENV OPAMYES true
RUN opam pin add QuickChick
