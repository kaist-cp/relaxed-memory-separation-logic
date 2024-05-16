FROM ubuntu:22.04

COPY ./pldi24-36-artifact /artifact
WORKDIR /artifact

RUN apt-get update && apt-get install -y \
        python3 \
        opam \
        libgmp-dev && \
    opam init --disable-sandboxing && \
    opam switch create . ocaml-system --no-install && \
    opam repo add coq-released https://coq.inria.fr/opam/released && \
    opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git && \
    opam pin add -n -y coq 8.16.1 && \
    OPAMFLAGS="-y --deps-only" make build-dep && \
    eval $(opam env) && \
    make -j
