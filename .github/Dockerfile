FROM coqorg/coq:8.20-ocaml-4.14-flambda

ENV NCPUS=4
ENV OPAMYES="true"
ENV OPAMJOBS=$NCPUS

RUN opam repo add coq-released https://coq.inria.fr/opam/released \
    && opam update \
    && opam install coq-equations coq-menhirlib menhir ppx_expect \
    && eval $(opam env)

RUN curl https://gitlab.com/api/v4/projects/4207231/packages/generic/graphviz-releases/12.1.1/graphviz-12.1.1.tar.gz -O \
    && tar -xzf graphviz-12.1.1.tar.gz \
    && cd graphviz-12.1.1 \
    && ./configure \
    && make \
    && sudo make install \
    && rm -rf graphviz-12.1.1.tar.gz graphviz-12.1.1

RUN sudo apt-get update -y -q \
    && DEBIAN_FRONTEND=noninteractive sudo apt-get install -y -q --no-install-recommends pandoc
