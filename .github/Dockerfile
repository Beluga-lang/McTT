FROM rocq/rocq-prover:9.0.0-native-ocaml-4.14.2-flambda

ENV NCPUS=4
ENV OPAMYES="true"
ENV OPAMJOBS=$NCPUS

RUN opam update \
    && opam install rocq-equations coq-menhirlib menhir ppx_expect ppx_inline_test \
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
