FROM coqorg/coq:8.9
COPY --chown=coq . QuickChick
ENV OPAMYES true
RUN opam pin add QuickChick
